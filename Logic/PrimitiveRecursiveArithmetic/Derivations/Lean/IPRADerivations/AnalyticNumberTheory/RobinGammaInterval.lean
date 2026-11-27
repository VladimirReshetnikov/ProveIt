import IPRADerivations.AnalyticNumberTheory.RobinLogName

/-!
# The lower Euler-constant name (`robin_ipra_research_2026-11-19`, `lem:gamma`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, Lemma `lem:gamma`: with
`a_m = H_m − log m − 1/(2m)`, `a_m ≤ γ ≤ a_m + 1/(12m²)`, by the finite telescoping
`a_{m+1} − a_m = 2z/(1 − z²) − 2 artanh z`, `z = 1/(2m+1)`; "Each displayed infinite sum can be replaced by a finite sum and
its explicit geometric tail."

The lower name telescopes from `a_1 = 1/2` with the *upper* logarithm names `U_K(z) = Un/Ud` of `RobinLogName`
(so it stays below the external `a_m`):

  `γ_lo(t, K) = 1/2 + Σ_{i<t} δU_K(1 + i)`,  `δU_K(m) = 2s/W − U_K(1/s) = nU/dU`,  `s = 2m + 1`, `W = 4m(m + 1)`.

* `un_le`: `U_K(1/s) ≤ 2s/W` (from `RobinGamma.q_inv`), so the numerators `nU = 2s(2K+1)D_K − Un_K` are exact (`nU_eq`);
* `term_lower`: for `K ≥ 2`, `δU_K(m) ≥ u/D` whenever `u/D ≤ 2s/W − U_2(1/s)` (a closed check), since `U_K ≤ U_2`
  (`RobinLogName.log_name`);
* the accumulators `An t K / Ad t K = Σ_{i<t} δU_K(1 + i)` (primitive recursions `accF`, `prodF`), nondecreasing in `t`
  (`acc_mono`);
* `gamma_lower`: for `t ≥ 3`, `K ≥ 2`, `Ad ≤ 14 An`, i.e. `γ_lo(t, K) ≥ 1/2 + 1/14 = 4/7`, from the three closed
  increments `δU_2(1) ≥ 0.056790`, `δU_2(2) ≥ 0.011200`, `δU_2(3) ≥ 0.003984`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lf Lv L_zero L_succ Pv P_succ P_zero sv Wv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName
  (Nz Nz_zero Nz_succ Dz Un Ud Lz log_name L_eq N_bridge Un_congr Ud_congr Ud_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The names at `K = 2` -/

abbrev k2 : PTm n := succ (succ zero)

theorem L_one (x : PTm n) : Γ ⊢[PRAAx] Lv (succ zero) x ≐ one :=
  (L_succ zero x).eqTrans ((congrMul (.eqRefl _) (L_zero x)).eqTrans (by ipra_ring))

theorem L_two (x : PTm n) : Γ ⊢[PRAAx] Lv k2 x ≐ succ two :=
  (L_succ (succ zero) x).eqTrans ((congrMul (.eqRefl _) (L_one x)).eqTrans (by ipra_ring))

theorem Nz_one (s : PTm n) : Γ ⊢[PRAAx] Nz (succ zero) one s ≐ two * (s * s) := by
  refine (Nz_succ zero one s).eqTrans ?_
  refine withEq (Nz_zero (Γ := Γ) one s) fun e0 => withEq (L_zero (Γ := Γ) (zero : PTm n)) fun e1 =>
    withEq (AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) (succ (two * zero))) fun e2 => ?_
  apply deriveNat; ipra_simps; rw [e0, e1, e2]; ring

theorem Nz_two (s : PTm n) :
    Γ ⊢[PRAAx] Nz k2 one s ≐ two * succ two * (s * s * (s * s)) + two * (s * s) := by
  refine (Nz_succ (succ zero) one s).eqTrans ?_
  refine withEq (Nz_one (Γ := Γ) s) fun e0 => withEq (L_one (Γ := Γ) (zero : PTm n)) fun e1 =>
    withEq (AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) (succ (two * succ zero))) fun e2 => ?_
  apply deriveNat; ipra_simps; rw [e0, e1, e2]; ring

theorem Pv_two (s : PTm n) : Γ ⊢[PRAAx] Pv k2 s ≐ s * s * s * s * s :=
  (P_succ (succ zero) s).eqTrans (congrMul (congrMul ((P_succ zero s).eqTrans
    (congrMul (congrMul (P_zero s) (.eqRefl _)) (.eqRefl _))) (.eqRefl _)) (.eqRefl _))

theorem Un_two (s W : PTm n) :
    Γ ⊢[PRAAx] Un k2 one s W ≐ num 30 * (s * s * (s * s)) * W + num 10 * (s * s) * W + num 6 * (s * s) := by
  refine withEq (Nz_two (Γ := Γ) s) fun e0 => withEq (L_two (Γ := Γ) (zero : PTm n)) fun e1 =>
    withEq (AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) (succ (two * k2))) fun e2 => ?_
  apply deriveNat; ipra_simps; rw [e0, e1, e2]; ring

theorem Ud_two (s W : PTm n) : Γ ⊢[PRAAx] Ud k2 one s W ≐ num 15 * W * (s * s * s * s * s) := by
  refine withEq (Pv_two (Γ := Γ) s) fun e0 => withEq (L_two (Γ := Γ) (zero : PTm n)) fun e1 => ?_
  apply deriveNat; ipra_simps; rw [e0, e1]; ring

/-! ## The increments `δU_K(m) = nU/dU` -/

abbrev Xm (m K : PTm n) : PTm n := two * sv m * succ (two * K) * Dz K one (sv m)
abbrev nU (m K : PTm n) : PTm n := monus (Xm m K) (Un K one (sv m) (Wv m))
abbrev dU (m K : PTm n) : PTm n := Ud K one (sv m) (Wv m)

theorem s_sq (m : PTm n) : Γ ⊢[PRAAx] sv m * sv m ≐ Wv m + one * one := by ipra_ring

theorem sv_pos (m : PTm n) : Γ ⊢[PRAAx] sv m ≐ succ (pred (sv m)) := pos_of_one_le (by ipra_le 𝔞 (two * m))

theorem Wv_pos {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] Wv m ≐ succ (pred (Wv m)) := by
  have q := le_mul_mono hm hm
  exact pos_of_one_le (by ipra_le sl q + 3 * 𝔞 (m * m) + 4 * 𝔞 m)

theorem dU_pos {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (K : PTm n) : Γ ⊢[PRAAx] dU m K ≐ succ (pred (dU m K)) :=
  Ud_pos (sv_pos m) (Wv_pos hm) K one

/-- `U_K(1/s) ≤ 2s/W`: the increments of the lower name are exact. -/
theorem un_le (m K : PTm n) : Γ ⊢[PRAAx] le (Un K one (sv m) (Wv m)) (Xm m K) := by
  have q := RobinGamma.q_inv (Γ := Γ) m K
  have eN := natEq (N_bridge (Γ := Γ) K (sv m))
  have eL := natEq (L_eq (Γ := Γ) K (sv m) zero)
  have e1 := natEq (AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) (succ (two * K)))
  ipra_le 𝔞 (succ (two * K)) * sl q + 𝔞 (two * two * K * Lv K (sv m) * (sv m * sv m)) with
    (2 * 𝔞 K + 1) * (4 * 𝔞 m * (𝔞 m + 1)) * eN -
      (2 * (2 * 𝔞 m + 1) * (2 * 𝔞 K + 1) * 𝔞 (Pv K (sv m)) - 2 * (2 * 𝔞 m + 1) ^ 2) * eL -
      2 * (2 * 𝔞 m + 1) ^ 2 * 𝔞 (Lv K zero) * e1

theorem nU_eq (m K : PTm n) : Γ ⊢[PRAAx] Xm m K ≐ Un K one (sv m) (Wv m) + nU m K := eq_add_of_le (un_le m K)

/-- For `K ≥ 2`: `δU_K(m) ≥ u/D` from the closed check `u/D ≤ 2s/W − U_2(1/s)`. -/
theorem term_lower {m j u D : PTm n} (hm : Γ ⊢[PRAAx] le one m)
    (hc : Γ ⊢[PRAAx] le (u * Wv m * Ud k2 one (sv m) (Wv m) + D * Wv m * Un k2 one (sv m) (Wv m))
      (D * (two * sv m) * Ud k2 one (sv m) (Wv m))) :
    Γ ⊢[PRAAx] le (u * dU m (succ (succ j))) (D * nU m (succ (succ j))) := by
  have nest := Prf.andE₂ (Prf.andE₁ (log_name (Γ := Γ) (p := one) (sv_pos m) (Wv_pos hm) (s_sq m) k2 j))
  have eK : Γ ⊢[PRAAx] k2 + j ≐ succ (succ j) := by ipra_ring
  have nest' := le_congr (congrMul (Un_congr _ _ _ eK) (.eqRefl _)) (congrMul (.eqRefl _) (Ud_congr _ _ _ eK)) nest
  have e := natEq (nU_eq (Γ := Γ) m (succ (succ j)))
  have c : Γ ⊢[PRAAx] le (Ud k2 one (sv m) (Wv m) * (u * dU m (succ (succ j))))
      (Ud k2 one (sv m) (Wv m) * (D * nU m (succ (succ j)))) := by
    ipra_le 𝔞 D * sl nest' + 𝔞 (succ (two * succ (succ j)) * Dz (succ (succ j)) one (sv m)) * sl hc with
      -(5 * (4 * 𝔞 m * (𝔞 m + 1)) * 𝔞 (Lv k2 zero) * 𝔞 (Pv k2 (sv m)) * 𝔞 D) * e
  have hp := Ud_pos (Γ := Γ) (sv_pos m) (Wv_pos hm) k2 one
  exact mul_le_cancel_at hp c

/-! ## The accumulated sums -/

/-- `nU` and `dU` at `m = i + 1`, over `0 = i`, `1 = K`. -/
def nUB : PTm 2 := nU (succ (var 0)) (var 1)
def dUB : PTm 2 := dU (succ (var 0)) (var 1)

theorem inst2_nUB (i K : PTm n) : inst2 nUB i K = nU (succ i) K := by simp [inst2, nUB]
theorem inst2_dUB (i K : PTm n) : inst2 dUB i K = dU (succ i) K := by simp [inst2, dUB]

/-- `A_{t+1} = A_t d_t + n_t D_t`, `D_t = Π_{i<t} d_i`: `A_t/D_t = Σ_{i<t} n_i/d_i`. -/
def accF : PR 2 := rec2 zero (var 1 * Syn.subst ![var 0, var 2] dUB +
  Syn.subst ![var 0, var 2] nUB * ap2 (prodF dUB) (var 0) (var 2))
abbrev An (t K : PTm n) : PTm n := ap2 accF t K
abbrev Ad (t K : PTm n) : PTm n := ap2 (prodF dUB) t K

theorem An_zero (K : PTm n) : Γ ⊢[PRAAx] An zero K ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (var 1 * Syn.subst ![var 0, var 2] dUB +
    Syn.subst ![var 0, var 2] nUB * ap2 (prodF dUB) (var 0) (var 2)) K
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem An_succ (t K : PTm n) : Γ ⊢[PRAAx] An (succ t) K ≐ An t K * dU (succ t) K + nU (succ t) K * Ad t K := by
  have h : Γ ⊢[PRAAx] ap2 accF (succ t) K ≐ Syn.subst ![t, ap2 accF t K, K]
      (var 1 * Syn.subst ![var 0, var 2] dUB + Syn.subst ![var 0, var 2] nUB * ap2 (prodF dUB) (var 0) (var 2)) :=
    rec2_succ (Γ := Γ) zero _ t K
  have e : Syn.subst ![t, ap2 accF t K, K]
      (var 1 * Syn.subst ![var 0, var 2] dUB + Syn.subst ![var 0, var 2] nUB * ap2 (prodF dUB) (var 0) (var 2)) =
      ap2 accF t K * inst2 dUB t K + inst2 nUB t K * ap2 (prodF dUB) t K := by
    have h1 : Syn.subst ![t, ap2 accF t K, K] (Syn.subst ![var 0, var 2] dUB) = inst2 dUB t K := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
    have h2 : Syn.subst ![t, ap2 accF t K, K] (Syn.subst ![var 0, var 2] nUB) = inst2 nUB t K := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
    simp only [PTm.subst_add, PTm.subst_mul, h1, h2, subst_ap2, Syn.subst_var]
    rfl
  rw [e, inst2_nUB, inst2_dUB] at h
  exact h

theorem Ad_zero (K : PTm n) : Γ ⊢[PRAAx] Ad zero K ≐ one := prod_zero _ _

theorem Ad_succ (t K : PTm n) : Γ ⊢[PRAAx] Ad (succ t) K ≐ Ad t K * dU (succ t) K := by
  have h := prod_succ (Γ := Γ) dUB t K
  have e : Syn.subst ![t, K] dUB = dU (succ t) K := inst2_dUB t K
  rw [e] at h
  exact h

theorem Ad_pos (t K : PTm n) : Γ ⊢[PRAAx] Ad t K ≐ succ (pred (Ad t K)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Ad (var 0) (Syn.shift K) ≐ succ (pred (Ad (var 0) (Syn.shift K)))) := by
    ipra_qfind (trivial) [subst_ap2]
    · exact (Ad_zero _).eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred (Ad_zero _).eqSymm)))
    · let Δ : List (Fm PTm (n + 1)) := (Ad (var 0) (Syn.shift K) ≐ succ (pred (Ad (var 0) (Syn.shift K)))) ::
        Γ.map Fm.shift
      have h0 := Ad_succ (Γ := Δ) (var 0) (Syn.shift K)
      have hm : Δ ⊢[PRAAx] le one (succ (var 0)) := by ipra_le 𝔞 (var 0)
      have p := Combinatorics.Binomial.pos_mul (Γ := Δ) Prf.hyp0 (dU_pos hm (Syn.shift K))
      exact h0.eqTrans (p.eqTrans (congrSucc (congrPred h0.eqSymm)))
  have r := Prf.allE t hall
  simpa [Syn.subst_inst_shift] using r

/-! ## The lower bound -/

abbrev t3 : PTm n := succ (succ (succ zero))

/-- The three closed increments: `Ad_3 ≤ 14 An_3` for `K ≥ 2`. -/
theorem three_terms (j : PTm n) : Γ ⊢[PRAAx] le (Ad t3 (succ (succ j))) (num 14 * An t3 (succ (succ j))) := by
  have h1 : Γ ⊢[PRAAx] le one (succ zero : PTm n) := le_refl _
  have h2 : Γ ⊢[PRAAx] le one (succ (succ zero) : PTm n) := by ipra_le 1
  have h3 : Γ ⊢[PRAAx] le one (succ (succ (succ zero)) : PTm n) := by ipra_le 2
  -- the closed checks
  have c1 : Γ ⊢[PRAAx] le (num 56790 * Wv (succ zero) * Ud k2 one (sv (succ zero)) (Wv (succ zero)) +
      num 1000000 * Wv (succ zero) * Un k2 one (sv (succ zero)) (Wv (succ zero)))
      (num 1000000 * (two * sv (succ zero)) * Ud k2 one (sv (succ zero)) (Wv (succ zero))) := by
    have u := natEq (Un_two (Γ := Γ) (sv (succ zero)) (Wv (succ zero)))
    have d := natEq (Ud_two (Γ := Γ) (sv (succ zero)) (Wv (succ zero)))
    ipra_le 28800 with (6000000 - 56790 * 8) * d - 8000000 * u
  have c2 : Γ ⊢[PRAAx] le (num 11200 * Wv (succ (succ zero)) * Ud k2 one (sv (succ (succ zero))) (Wv (succ (succ zero))) +
      num 1000000 * Wv (succ (succ zero)) * Un k2 one (sv (succ (succ zero))) (Wv (succ (succ zero))))
      (num 1000000 * (two * sv (succ (succ zero))) * Ud k2 one (sv (succ (succ zero))) (Wv (succ (succ zero)))) := by
    have u := natEq (Un_two (Γ := Γ) (sv (succ (succ zero))) (Wv (succ (succ zero))))
    have d := natEq (Ud_two (Γ := Γ) (sv (succ (succ zero))) (Wv (succ (succ zero))))
    ipra_le 0 with (10000000 - 11200 * 24) * d - 24000000 * u
  have c3 : Γ ⊢[PRAAx] le (num 3984 * Wv t3 * Ud k2 one (sv t3) (Wv t3) +
      num 1000000 * Wv t3 * Un k2 one (sv t3) (Wv t3))
      (num 1000000 * (two * sv t3) * Ud k2 one (sv t3) (Wv t3)) := by
    have u := natEq (Un_two (Γ := Γ) (sv t3) (Wv t3))
    have d := natEq (Ud_two (Γ := Γ) (sv t3) (Wv t3))
    ipra_le 261918720 with (14000000 - 3984 * 48) * d - 48000000 * u
  have l1 := term_lower (j := j) h1 c1
  have l2 := term_lower (j := j) h2 c2
  have l3 := term_lower (j := j) h3 c3
  -- unfold the sums
  have a1 := natEq (An_succ (Γ := Γ) zero (succ (succ j)))
  have a2 := natEq (An_succ (Γ := Γ) (succ zero) (succ (succ j)))
  have a3 := natEq (An_succ (Γ := Γ) (succ (succ zero)) (succ (succ j)))
  have a0 := natEq (An_zero (Γ := Γ) (succ (succ j)))
  have d1 := natEq (Ad_succ (Γ := Γ) zero (succ (succ j)))
  have d2 := natEq (Ad_succ (Γ := Γ) (succ zero) (succ (succ j)))
  have d3 := natEq (Ad_succ (Γ := Γ) (succ (succ zero)) (succ (succ j)))
  have d0 := natEq (Ad_zero (Γ := Γ) (succ (succ j)))
  have eA : Γ ⊢[PRAAx] An t3 (succ (succ j)) ≐ nU (succ zero) (succ (succ j)) * dU (succ (succ zero)) (succ (succ j)) *
      dU t3 (succ (succ j)) + nU (succ (succ zero)) (succ (succ j)) * dU (succ zero) (succ (succ j)) *
      dU t3 (succ (succ j)) + nU t3 (succ (succ j)) * dU (succ zero) (succ (succ j)) * dU (succ (succ zero)) (succ (succ j)) := by
    apply deriveNat; ipra_simps; rw [a3, a2, a1, a0, d2, d1, d0]; ring
  have eD : Γ ⊢[PRAAx] Ad t3 (succ (succ j)) ≐ dU (succ zero) (succ (succ j)) * dU (succ (succ zero)) (succ (succ j)) *
      dU t3 (succ (succ j)) := by
    apply deriveNat; ipra_simps; rw [d3, d2, d1, d0]; ring
  have fA := natEq eA
  have fD := natEq eD
  have c : Γ ⊢[PRAAx] le (num 1000000 * Ad t3 (succ (succ j))) (num 1000000 * (num 14 * An t3 (succ (succ j)))) := by
    ipra_le 14 * 𝔞 (dU (succ (succ zero)) (succ (succ j)) * dU t3 (succ (succ j))) * sl l1 +
      14 * 𝔞 (dU (succ zero) (succ (succ j)) * dU t3 (succ (succ j))) * sl l2 +
      14 * 𝔞 (dU (succ zero) (succ (succ j)) * dU (succ (succ zero)) (succ (succ j))) * sl l3 +
      7636 * 𝔞 (dU (succ zero) (succ (succ j)) * dU (succ (succ zero)) (succ (succ j)) * dU t3 (succ (succ j)))
      with 14000000 * fA - 1000000 * fD
  exact mul_le_cancel (d' := num 999999) c

/-- The lower name is nondecreasing in `t`: `A_3/D_3 ≤ A_{3+i}/D_{3+i}`. -/
abbrev MF (i K : PTm n) : Fm PTm n := le (An t3 K * Ad (t3 + i) K) (An (t3 + i) K * Ad t3 K)

theorem acc_step (i K : PTm n) (ih : Γ ⊢[PRAAx] MF i K) : Γ ⊢[PRAAx] MF (succ i) K := by
  have e : Γ ⊢[PRAAx] t3 + succ i ≐ succ (t3 + i) := add_succ _ _
  have eA := An_succ (Γ := Γ) (t3 + i) K
  have eD := Ad_succ (Γ := Γ) (t3 + i) K
  have eA' : Γ ⊢[PRAAx] An (t3 + succ i) K ≐ An (t3 + i) K * dU (succ (t3 + i)) K + nU (succ (t3 + i)) K * Ad (t3 + i) K :=
    (congrAp2 _ e (.eqRefl _)).eqTrans eA
  have eD' : Γ ⊢[PRAAx] Ad (t3 + succ i) K ≐ Ad (t3 + i) K * dU (succ (t3 + i)) K :=
    (congrAp2 _ e (.eqRefl _)).eqTrans eD
  refine le_congr (congrMul (.eqRefl _) eD').eqSymm (congrMul eA' (.eqRefl _)).eqSymm ?_
  ipra_le 𝔞 (dU (succ (t3 + i)) K) * sl ih + 𝔞 (nU (succ (t3 + i)) K * Ad (t3 + i) K * Ad t3 K)

theorem acc_mono (i K : PTm n) : Γ ⊢[PRAAx] MF i K := by
  have hall : Γ ⊢[PRAAx] Fm.all (MF (var 0) (Syn.shift K)) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
    · have e : Γ ⊢[PRAAx] t3 + zero ≐ t3 := add_zero _
      exact le_congr (congrMul (.eqRefl _) (congrAp2 _ e (.eqRefl _)).eqSymm)
        (congrMul (congrAp2 _ e (.eqRefl _)).eqSymm (.eqRefl _)) (le_refl _)
    · exact acc_step _ _ Prf.hyp0
  have r := Prf.allE i hall
  simpa [Syn.subst_inst_shift] using r

/-- `γ_lo(t, K) ≥ 4/7` for `t ≥ 3`, `K ≥ 2`: `Ad_t ≤ 14 An_t`. -/
theorem gamma_lower (i j : PTm n) :
    Γ ⊢[PRAAx] le (Ad (t3 + i) (succ (succ j))) (num 14 * An (t3 + i) (succ (succ j))) := by
  have b := three_terms (Γ := Γ) j
  have m := acc_mono (Γ := Γ) i (succ (succ j))
  have m1 := le_mul_mono b (le_refl (Ad (t3 + i) (succ (succ j))))
  have h1 : Γ ⊢[PRAAx] le one (succ zero : PTm n) := le_refl _
  have h2 : Γ ⊢[PRAAx] le one (succ (succ zero) : PTm n) := by ipra_le 1
  have h3 : Γ ⊢[PRAAx] le one (succ (succ (succ zero)) : PTm n) := by ipra_le 2
  have p1 := dU_pos h1 (succ (succ j))
  have p2 := dU_pos h2 (succ (succ j))
  have p3 := dU_pos h3 (succ (succ j))
  have d1 := natEq (Ad_succ (Γ := Γ) zero (succ (succ j)))
  have d2 := natEq (Ad_succ (Γ := Γ) (succ zero) (succ (succ j)))
  have d3 := natEq (Ad_succ (Γ := Γ) (succ (succ zero)) (succ (succ j)))
  have d0 := natEq (Ad_zero (Γ := Γ) (succ (succ j)))
  have eD3 : Γ ⊢[PRAAx] Ad t3 (succ (succ j)) ≐
      dU (succ zero) (succ (succ j)) * dU (succ (succ zero)) (succ (succ j)) * dU t3 (succ (succ j)) := by
    apply deriveNat; ipra_simps; rw [d3, d2, d1, d0]; ring
  have q := Combinatorics.Binomial.pos_mul (Combinatorics.Binomial.pos_mul p1 p2) p3
  have hp : Γ ⊢[PRAAx] Ad t3 (succ (succ j)) ≐ succ (pred (Ad t3 (succ (succ j)))) :=
    eD3.eqTrans (q.eqTrans (congrSucc (congrPred eD3.eqSymm)))
  have c : Γ ⊢[PRAAx] le (Ad t3 (succ (succ j)) * Ad (t3 + i) (succ (succ j)))
      (Ad t3 (succ (succ j)) * (num 14 * An (t3 + i) (succ (succ j)))) := by
    ipra_le sl m1 + 14 * sl m
  exact mul_le_cancel_at hp c

end LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval
