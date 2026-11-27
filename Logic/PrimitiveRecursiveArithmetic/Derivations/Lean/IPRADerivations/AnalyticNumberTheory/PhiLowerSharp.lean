import IPRADerivations.AnalyticNumberTheory.PhiTwo

/-!
# The sharp lower bound `φ(n)² ≥ n` for `n ∉ {2, 6}`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-lower`
(second part): `φ(n)² ≥ n` for every `n ∉ {2, 6}`.

* `ppow_sq2`: `φ(p^a)² ≥ 2 p^a` for an odd prime power `p^a ≠ 3`;
* `phi_sq_odd2`: `φ(m)² ≥ 2m` for odd `m ∉ {1, 3}`, by strong induction peeling `p = lpf(m)`:
  the cofactor `m′` is never `3` (else `lpf(m) ≤ 3` forces `p = 3 ∣ m′`), and `m′ = 1` is the
  prime-power case;
* `phi_sq`: with `n = 2^a m`, `m` odd: `a = 0` is `PhiLower.phi_sq_odd`; `a = 1` uses
  `phi_sq_odd2` (as `n ≠ 2, 6`); `a ≥ 2` uses `4^{a−1} ≥ 2^a`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiLowerSharp

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf μz lpfBody lpf_dvd lpf_prime prime eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower
open LeanProofs.IPRA.AnalyticNumberTheory.PhiTwo (three four six phi_congr')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The local bound -/

/-- `(p − 1)² ≥ 2p` for `p ≥ 4`. -/
theorem sq_pred_ge2 {p : PTm n} (h : Γ ⊢[PRAAx] le four p) :
    Γ ⊢[PRAAx] le (two * p) (monus p one * monus p one) := by
  have e := natEq (eq_add_of_le h)
  have e' : Γ ⊢[PRAAx] monus p one ≐ succ (succ (succ (monus p four))) :=
    (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (by
      refine (congrMonus (by ipra_ring :
        Γ ⊢[PRAAx] four + monus p four ≐ succ (succ (succ (monus p four))) + one) (.eqRefl _)).eqTrans ?_
      exact add_monus _ _)
  refine le_of_eq_add (d := monus p four * monus p four + succ (succ (succ (succ zero))) * monus p four + one) ?_
  ipra_lc (Groth.ι (Q.mk _ (monus p one)) + Groth.ι (Q.mk _ (monus p four)) + 3) * natEq e' - 2 * e

theorem ppow_sq2_big {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h4 : Γ ⊢[PRAAx] le four p) (k : PTm n) :
    Γ ⊢[PRAAx] le (two * pw p (succ k)) (phi (pw p (succ k)) * phi (pw p (succ k))) := by
  have hQ := pw_pos' (prime_eq_succ_pred hp) k
  have l₁ : Γ ⊢[PRAAx] le (pw p k * one) (pw p k * pw p k) := le_mul_mono (le_refl _) (one_le_of_pos hQ)
  have l := le_mul_mono l₁ (sq_pred_ge2 h4)
  have e := phi_ppow hp k
  refine le_congr ?_ (.eqTrans ?_ (congrMul e e).eqSymm) l
  · refine .eqTrans ?_ (congrMul (.eqRefl _) (pw_succ _ _)).eqSymm
    ipra_ring
  · ipra_ring

theorem ppow_sq2_three {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hp3 : Γ ⊢[PRAAx] p ≐ three) (j : PTm n) :
    Γ ⊢[PRAAx] le (two * pw p (succ (succ j))) (phi (pw p (succ (succ j))) * phi (pw p (succ (succ j)))) := by
  have hq := pw_pos' (prime_eq_succ_pred hp) j
  have hpQ : Γ ⊢[PRAAx] le p (pw p (succ j)) := by
    refine le_of_eq_add (d := pred (pw p j) * p) ?_
    ipra_lc natEq (pw_succ p j) + Groth.ι (Q.mk _ p) * natEq hq
  have h3Q := le_congr hp3 (.eqRefl _) hpQ
  have e₁ := natEq (phi_ppow hp (succ j))
  have e₂ := natEq (pw_succ (Γ := Γ) p (succ j))
  refine le_of_eq_add (d := pw p (succ j) * (six + four * monus (pw p (succ j)) three)) ?_
  ipra_lc (Groth.ι (Q.mk _ (phi (pw p (succ (succ j))))) + Groth.ι (Q.mk _ (pw p (succ j))) * Groth.ι (Q.mk _ (monus p one))) * e₁ +
    Groth.ι (Q.mk _ (pw p (succ j))) * Groth.ι (Q.mk _ (pw p (succ j))) * (Groth.ι (Q.mk _ (monus p one)) + 2) * natEq ((congrMonus hp3 (.eqRefl one)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))) -
    2 * e₂ - 2 * Groth.ι (Q.mk _ (pw p (succ j))) * natEq hp3 +
    4 * Groth.ι (Q.mk _ (pw p (succ j))) * natEq (eq_add_of_le h3Q)

/-- `φ(p^{k+1})² ≥ 2 p^{k+1}` for an odd prime power `p^{k+1} ≠ 3`. -/
theorem ppow_sq2 {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h3 : Γ ⊢[PRAAx] le three p) (k : PTm n)
    (hne : Γ ⊢[PRAAx] neg (pw p (succ k) ≐ three)) :
    Γ ⊢[PRAAx] le (two * pw p (succ k)) (phi (pw p (succ k)) * phi (pw p (succ k))) := by
  refine .orE (lt_or_eq_of_le h3) (ppow_sq2_big hp.wk Prf.hyp0 k) ?_
  refine .orE (zero_or_succ k) ?_ ?_
  · exact .botE _ (.impE hne.wk.wk ((congrAp2 powF (congrSucc Prf.hyp0) (.eqRefl _)).eqTrans
      ((pw_one _).eqTrans Prf.hyp1.eqSymm)))
  · have e : ((k ≐ succ (pred k)) :: (three ≐ p) :: Γ) ⊢[PRAAx] pw p (succ k) ≐ pw p (succ (succ (pred k))) :=
      congrAp2 powF (congrSucc Prf.hyp0) (.eqRefl _)
    exact le_congr (congrMul (.eqRefl _) e.eqSymm) (congrMul (phi_congr' e) (phi_congr' e)).eqSymm
      (ppow_sq2_three hp.wk.wk Prf.hyp1.eqSymm (pred k))

/-! ## `φ(m)² ≥ 2m` for odd `m ∉ {1, 3}` -/

/-- `(m mod 2)(1 ∸ [m = 1])(1 ∸ [m = 3]) sg(2m ∸ φ(m)²)`, over `0 = m`, `1 = x`. -/
abbrev o2B : PTm 2 := rem (var 0) two * monus one (eqb (var 0) one) * monus one (eqb (var 0) three) *
  sg (monus (two * var 0) (phi (var 0) * phi (var 0)))

theorem inst2_o2 (M x : PTm n) : inst2 o2B M x = rem M two * monus one (eqb M one) * monus one (eqb M three) *
    sg (monus (two * M) (phi M * phi M)) := by simp [inst2]

alias not_one := LeanProofs.IPRA.Common.eqb_compl_one_of_ne

/-- Reading the claim off a vanishing term. -/
theorem o2_read {M x : PTm n} (hodd : Γ ⊢[PRAAx] rem M two ≐ one) (h1 : Γ ⊢[PRAAx] neg (M ≐ one))
    (h3 : Γ ⊢[PRAAx] neg (M ≐ three)) (h : Γ ⊢[PRAAx] inst2 o2B M x ≐ zero) :
    Γ ⊢[PRAAx] le (two * M) (phi M * phi M) := by
  rw [inst2_o2] at h
  refine PhiDivides.sg_zero_inv (.eqTrans ?_ h)
  refine .eqTrans ?_ (congrMul (congrMul (congrMul hodd (not_one h1)) (not_one h3)) (.eqRefl _)).eqSymm
  ipra_ring

/-- `lpf(n) ≤ 3` when `3 ∣ n`. -/
theorem lpf_le_three {N : PTm n} (hN : Γ ⊢[PRAAx] lt one N) (h : Γ ⊢[PRAAx] dvd three N) :
    Γ ⊢[PRAAx] le (lpf N) three := by
  have s := Search.search_found (f := lpfBody) (N := N) (x := N) (i := one) (by rw [Primes.inst2_lpf]; exact h) hN
  exact (succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (Prf.andE₂ (Prf.andE₂ s)))

open LeanProofs.IPRA.AnalyticNumberTheory.Radical (val_pos cof_rem_pos cof_lt)

/-- The step for odd `N ∉ {1, 3}`, peeling its least prime factor `p`. -/
theorem d2_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) (hlpf : Γ ⊢[PRAAx] lpf N ≐ p) (hodd : Γ ⊢[PRAAx] rem N two ≐ one)
    (h1 : Γ ⊢[PRAAx] neg (N ≐ one)) (h3 : Γ ⊢[PRAAx] neg (N ≐ three))
    (hV : Γ ⊢[PRAAx] ap2 (sumF o2B) N x ≐ zero) :
    Γ ⊢[PRAAx] le (two * N) (phi N * phi N) := by
  have hpo := prime_odd hp hpN hodd
  have h3p := three_le_of_odd_prime hp hpo
  have hrm := cof_rem_pos hN hp hpN
  obtain ⟨hm, hNe, hmul⟩ := prime_power_totient_split hN hp
  have e₂ := congrAp2 powF (val_pos hN hp hpN).eqSymm (.eqRefl p)
  have hmo := odd_right_factor hNe hodd
  have h₀ := sum_zero_elim o2B hV (cof_lt hN hp hpN)
  have hsq := le_congr e₂ (congrMul (phi_congr' e₂) (phi_congr' e₂)) (ppow_sq hp h3p (pred (val p N)))
  refine .orE (eq_or_ne (quo N (pw p (val p N))) one) ?_ ?_
  · -- `N = p^a`, a prime power `≠ 3`.
    have eN : ((quo N (pw p (val p N)) ≐ one) :: Γ) ⊢[PRAAx] N ≐ pw p (succ (pred (val p N))) :=
      hNe.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans ((EulerProduct.mul_one' _).eqTrans e₂.wk.eqSymm))
    have hne : ((quo N (pw p (val p N)) ≐ one) :: Γ) ⊢[PRAAx] neg (pw p (succ (pred (val p N))) ≐ three) :=
      .impI (.impE h3.wk.wk (eN.wk.eqTrans Prf.hyp0))
    have l := ppow_sq2 hp.wk h3p.wk (pred (val p N)) hne
    exact le_congr (congrMul (.eqRefl _) eN.eqSymm) (congrMul (phi_congr' eN) (phi_congr' eN)).eqSymm l
  · have hm1 : (neg (quo N (pw p (val p N)) ≐ one) :: Γ) ⊢[PRAAx] neg (quo N (pw p (val p N)) ≐ one) := Prf.hyp0
    -- The cofactor is not `3`.
    have hm3 : (neg (quo N (pw p (val p N)) ≐ one) :: Γ) ⊢[PRAAx] neg (quo N (pw p (val p N)) ≐ three) := by
      refine .impI ?_
      have d3 : ((quo N (pw p (val p N)) ≐ three) :: neg (quo N (pw p (val p N)) ≐ one) :: Γ) ⊢[PRAAx]
          dvd three N :=
        dvd_congr hNe.wk.wk.eqSymm (dvd_congr (mul_comm _ _) (dvd_mul' (congrSucc (pred_succ _).eqSymm) _
          (dvd_congr_left Prf.hyp0 (dvd_self' (hm.wk.wk)))))
      have h1N : ((quo N (pw p (val p N)) ≐ three) :: neg (quo N (pw p (val p N)) ≐ one) :: Γ) ⊢[PRAAx]
          lt one N := by
        refine .orE (lt_or_le one N) Prf.hyp0 ?_
        refine .botE _ (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
        · exact succ_ne_zero' _ (hN.wk.wk.wk.wk.eqSymm.eqTrans ((monus_zero _).eqSymm.eqTrans
            ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)))
        · exact .impE h1.wk.wk.wk.wk Prf.hyp0
      have hp3 := le_antisymm (le_congr hlpf.wk.wk (.eqRefl _) (lpf_le_three h1N d3)) h3p.wk.wk
      exact succ_ne_zero' _ (hrm.wk.wk.eqSymm.eqTrans ((congrAp2 remF Prf.hyp0 hp3).eqTrans
        (dvd_self' (congrSucc (pred_succ _).eqSymm))))
    -- The induction hypothesis at the cofactor.
    have ih := o2_read hmo.wk hm1 hm3 h₀.wk
    have l := le_mul_mono hsq.wk ih
    refine le_congr ?_ ?_ l
    · refine .eqTrans ?_ (congrMul (.eqRefl _) hNe.wk).eqSymm
      ipra_ring
    · refine .eqTrans ?_ (congrMul hmul.wk hmul.wk).eqSymm
      ipra_ring

theorem d2_main {N x : PTm n} (hodd : Γ ⊢[PRAAx] rem N two ≐ one) (h1 : Γ ⊢[PRAAx] neg (N ≐ one))
    (h3 : Γ ⊢[PRAAx] neg (N ≐ three)) (hV : Γ ⊢[PRAAx] ap2 (sumF o2B) N x ≐ zero) :
    Γ ⊢[PRAAx] le (two * N) (phi N * phi N) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact .botE _ (succ_ne_zero (a := zero) (hodd.wk.eqSymm.eqTrans
      ((congrAp2 remF Prf.hyp0 (.eqRefl _)).eqTrans (rem_zero _))))
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · exact .botE _ (.impE h1.wk.wk (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))
  · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx]
        N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    exact d2_found Prf.hyp1 (lpf_prime _) (dvd_congr e.eqSymm (Prf.andE₁ (lpf_dvd _))) (lpf_congr e)
      hodd.wk.wk h1.wk.wk h3.wk.wk hV.wk.wk

theorem zero4 (A B C D : PTm n) (h : Γ ⊢[PRAAx] A ≐ zero ⋎ (B ≐ zero ⋎ C ≐ zero)) :
    Γ ⊢[PRAAx] A * B * C * D ≐ zero := by
  refine .orE h ?_ (.orE Prf.hyp0 ?_ ?_)
  · exact (congrMul (congrMul (congrMul Prf.hyp0 (.eqRefl _)) (.eqRefl _)) (.eqRefl _)).eqTrans
      (by ipra_ring)
  · exact (congrMul (congrMul (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)) (.eqRefl _)).eqTrans
      (by ipra_ring)
  · exact (congrMul (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans
      (by ipra_ring)

theorem d2_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF o2B) N x ≐ zero) : Γ ⊢[PRAAx] inst2 o2B N x ≐ zero := by
  rw [inst2_o2]
  refine .orE (zero_or_succ (rem N two)) (zero4 _ _ _ _ (.orI₁ Prf.hyp0)) ?_
  have hodd : ((rem N two ≐ succ (pred (rem N two))) :: Γ) ⊢[PRAAx] rem N two ≐ one :=
    eq_one_of_lt_two (rem_lt' two_pos' N) (.impI (succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans Prf.hyp0)))
  refine .orE (eq_or_ne N one) (zero4 _ _ _ _ (.orI₂ (.orI₁ ((congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))))) ?_
  refine .orE (eq_or_ne N three) (zero4 _ _ _ _ (.orI₂ (.orI₂ ((congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))))) ?_
  have l := d2_main hodd.wk.wk Prf.hyp1 Prf.hyp0 hV.wk.wk.wk
  exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) l)).eqTrans sg_zero)).eqTrans
    (mul_zero _)

private abbrev o2F : Fm PTm 2 := ap2 (sumF o2B) (var 0) (var 1) ≐ zero

private theorem o2₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] o2F := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · exact (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 (d2_step Prf.hyp0)).eqTrans (add_zero _))

/-- `φ(m)² ≥ 2m` for odd `m ∉ {1, 3}`. -/
theorem phi_sq_odd2 {M : PTm n} (hodd : Γ ⊢[PRAAx] rem M two ≐ one) (h1 : Γ ⊢[PRAAx] neg (M ≐ one))
    (h3 : Γ ⊢[PRAAx] neg (M ≐ three)) : Γ ⊢[PRAAx] le (two * M) (phi M * phi M) := by
  have h := inst (Γ := Γ) o2₀ (![succ M, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact o2_read hodd h1 h3 (sum_zero_elim_last o2B h)

/-! ## `φ(n)² ≥ n` for `n ∉ {2, 6}` -/

theorem phi_sq_even {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (h2 : Γ ⊢[PRAAx] neg (N ≐ two))
    (h6 : Γ ⊢[PRAAx] neg (N ≐ six)) (ha : Γ ⊢[PRAAx] val two N ≐ succ (pred (val two N))) :
    Γ ⊢[PRAAx] le N (phi N * phi N) := by
  obtain ⟨hNe, hφ, hmo, _⟩ := two_adic_totient_split hN ha
  have hsqo := phi_sq_odd hmo
  refine .orE (zero_or_succ (pred (val two N))) ?_ ?_
  · -- `a = 1`: `n = 2m`, `φ(n) = φ(m)`, `m ∉ {1, 3}`.
    have hk : ((pred (val two N) ≐ zero) :: Γ) ⊢[PRAAx] pw two (pred (val two N)) ≐ one :=
      (congrAp2 powF Prf.hyp0 (.eqRefl _)).eqTrans (pw_zero _)
    have hk1 : ((pred (val two N) ≐ zero) :: Γ) ⊢[PRAAx] pw two (succ (pred (val two N))) ≐ two :=
      (congrAp2 powF (congrSucc Prf.hyp0) (.eqRefl _)).eqTrans (pw_one _)
    have eN : ((pred (val two N) ≐ zero) :: Γ) ⊢[PRAAx] N ≐ two * quo N (pw two (val two N)) :=
      hNe.wk.eqTrans (congrMul hk1 (.eqRefl _))
    have eφ : ((pred (val two N) ≐ zero) :: Γ) ⊢[PRAAx] phi N ≐ phi (quo N (pw two (val two N))) :=
      hφ.wk.eqTrans ((congrMul hk (.eqRefl _)).eqTrans (one_mul _))
    have m1 : ((pred (val two N) ≐ zero) :: Γ) ⊢[PRAAx] neg (quo N (pw two (val two N)) ≐ one) :=
      .impI (.impE h2.wk.wk (eN.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans
        (by ipra_ring))))
    have m3 : ((pred (val two N) ≐ zero) :: Γ) ⊢[PRAAx] neg (quo N (pw two (val two N)) ≐ three) :=
      .impI (.impE h6.wk.wk (eN.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans
        (by ipra_ring))))
    exact le_congr eN.eqSymm (congrMul eφ eφ).eqSymm (phi_sq_odd2 hmo.wk m1 m3)
  · -- `a ≥ 2`: `φ(n)² = Q² φ(m)² ≥ 2Q m = n` with `Q = 2^{a−1} ≥ 2`.
    have hQ := pw_pos' (two_pos' (Γ := (pred (val two N) ≐ succ (pred (pred (val two N)))) :: Γ)) (pred (pred (val two N)))
    have e₃ : ((pred (val two N) ≐ succ (pred (pred (val two N)))) :: Γ) ⊢[PRAAx]
        pw two (pred (val two N)) ≐ pw two (pred (pred (val two N))) * two :=
      (congrAp2 powF Prf.hyp0 (.eqRefl _)).eqTrans (pw_succ _ _)
    have lQ : ((pred (val two N) ≐ succ (pred (pred (val two N)))) :: Γ) ⊢[PRAAx]
        le two (pw two (pred (val two N))) :=
      le_congr (one_mul _) e₃.eqSymm (le_mul_mono (one_le_of_pos hQ) (le_refl two))
    have l := le_mul_mono (le_mul_mono (le_refl (pw two (pred (val two N)))) lQ) hsqo.wk
    refine le_congr ?_ ?_ l
    · ipra_lc -natEq (hNe.wk : ((pred (val two N) ≐ succ (pred (pred (val two N)))) :: Γ) ⊢[PRAAx] _) -
        Groth.ι (Q.mk _ (quo N (pw two (val two N)))) * natEq (pw_succ (Γ := (pred (val two N) ≐ succ (pred (pred (val two N)))) :: Γ) two (pred (val two N)))
    · ipra_lc -(Groth.ι (Q.mk _ (phi N)) + Groth.ι (Q.mk _ (pw two (pred (val two N)))) * Groth.ι (Q.mk _ (phi (quo N (pw two (val two N)))))) * natEq (hφ.wk : ((pred (val two N) ≐ succ (pred (pred (val two N)))) :: Γ) ⊢[PRAAx] _)

/-- `thm:phi-lower` (second part) at an arbitrary `n`: `φ(n)² ≥ n` for `n ∉ {2, 6}`. -/
theorem phi_sq_at {N : PTm n} (h2 : Γ ⊢[PRAAx] neg (N ≐ two)) (h6 : Γ ⊢[PRAAx] neg (N ≐ six)) :
    Γ ⊢[PRAAx] le N (phi N * phi N) := by
  refine .orE (zero_or_succ N) ((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)) ?_
  have hN : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
  refine .orE (zero_or_succ (val two N)) ?_ (phi_sq_even hN.wk h2.wk.wk h6.wk.wk Prf.hyp0)
  exact phi_sq_odd (odd_of_zero_two_valuation hN.wk Prf.hyp0)

/-- `thm:phi-lower` (second part): `φ(n)² ≥ n` for every `n ∉ {2, 6}`. -/
abbrev phiSqFormula : Fm PTm 1 :=
  neg (var 0 ≐ two) ⟶ neg (var 0 ≐ six) ⟶ le (var 0) (phi (var 0) * phi (var 0))

theorem phi_sq : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiSqFormula :=
  closeUniv 1 (.impI (.impI (phi_sq_at Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiLowerSharp
