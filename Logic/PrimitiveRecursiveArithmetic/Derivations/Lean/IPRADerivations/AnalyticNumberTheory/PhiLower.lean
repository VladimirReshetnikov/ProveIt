import IPRADerivations.AnalyticNumberTheory.TotientCorollaries

/-!
# The elementary lower bound `2 φ(n)² ≥ n`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-lower`
(first part): `2 φ(n)² ≥ n` for every `n`.

* `phi_sq_odd`: `φ(n)² ≥ n` for odd `n`, by strong induction peeling the odd prime `p = lpf(n)`:
  `φ(p^a)² = p^{2a−2} (p − 1)² ≥ p^a` since `(p − 1)² ≥ p` for `p ≥ 3`;
* `phi_lower`: split `n = 2^a m` with `m` odd once; `φ(2^{k+1}) = 2^k` and `2 · 4^k ≥ 2^{k+1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiLower

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody coprime_pow totient_prime_power_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (val_pos cof_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Inequality helpers -/

alias le_mul_mono := Common.mul_le_mul

alias one_le_pos := Common.one_le_of_pos

/-- `(p − 1)² ≥ p` for `p ≥ 3`. -/
theorem sq_pred_ge {p : PTm n} (h : Γ ⊢[PRAAx] le (succ two) p) :
    Γ ⊢[PRAAx] le p (monus p one * monus p one) := by
  have e := natEq (eq_add_of_le h)
  have e' : Γ ⊢[PRAAx] monus p one ≐ succ (succ (monus p (succ two))) :=
    (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (by
      refine (congrMonus (by ipra_ring :
        Γ ⊢[PRAAx] succ two + monus p (succ two) ≐ succ (succ (monus p (succ two))) + one) (.eqRefl _)).eqTrans ?_
      exact add_monus _ _)
  refine le_of_eq_add (d := monus p (succ two) * monus p (succ two) + succ two * monus p (succ two) + one) ?_
  ipra_lc -e + (Groth.ι (Q.mk _ (monus p one)) + Groth.ι (Q.mk _ (monus p (succ two))) + 2) * natEq e'

/-! ## Odd primes -/

/-- A prime divisor of an odd number is odd. -/
theorem prime_odd {N p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpN : Γ ⊢[PRAAx] dvd p N)
    (hodd : Γ ⊢[PRAAx] rem N two ≐ one) : Γ ⊢[PRAAx] rem p two ≐ one := by
  refine eq_one_of_lt_two (rem_lt' two_pos' p) (.impI ?_)
  -- `2 ∣ p` forces `p = 2`, and then `2 ∣ N`.
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  have hp' := hp
  unfold prime at hp'
  have hall := Prf.allE two (Prf.andE₂ hp')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hall
  refine .orE (lt_or_eq_of_le hp2.wk) ?_ ?_
  · exact .impE (.impE (.impE hall.wk.wk (le_refl _)) Prf.hyp0) Prf.hyp1
  · exact succ_ne_zero' _ (a := zero) (hodd.wk.wk.eqSymm.eqTrans (dvd_trans' two_pos' (prime_eq_succ_pred hp).wk.wk
      Prf.hyp1 hpN.wk.wk))

/-- An odd prime is `≥ 3`. -/
theorem three_le_of_odd_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] rem p two ≐ one) :
    Γ ⊢[PRAAx] le (succ two) p := by
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  refine .orE (lt_or_eq_of_le hp2) Prf.hyp0 ?_
  have r : ((two ≐ p) :: Γ) ⊢[PRAAx] rem p two ≐ zero :=
    (congrAp2 remF Prf.hyp0.eqSymm (.eqRefl _)).eqTrans (dvd_self' two_pos')
  exact succ_ne_zero' _ (hodd.wk.eqSymm.eqTrans r)

/-- `2` is prime. -/
theorem prime_two : Γ ⊢[PRAAx] prime (two : PTm n) := by
  have d := lpf_dvd (Γ := Γ) (zero : PTm n)
  have e : Γ ⊢[PRAAx] lpf (succ (succ (zero : PTm n))) ≐ two :=
    le_antisymm (Prf.andE₂ d) (two_le_lpf _)
  exact prime_congr e (lpf_prime _)

/-- `φ(p^{k+1}) = p^k (p − 1)`. -/
theorem phi_ppow {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (k : PTm n) :
    Γ ⊢[PRAAx] phi (pw p (succ k)) ≐ pw p k * monus p one := by
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  ipra_lc natEq (totient_prime_power_at (k := k) hp) + natEq (pw_succ p k) +
    Groth.ι (Q.mk _ (pw p k)) * natEq (eq_add_of_le (le_trans (le_succ_self one) hp2))

/-- `φ(p^{k+1})² ≥ p^{k+1}` for an odd prime `p`. -/
theorem ppow_sq {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h3 : Γ ⊢[PRAAx] le (succ two) p) (k : PTm n) :
    Γ ⊢[PRAAx] le (pw p (succ k)) (phi (pw p (succ k)) * phi (pw p (succ k))) := by
  have hQ := pw_pos' (prime_eq_succ_pred hp) k
  have l₁ : Γ ⊢[PRAAx] le (one * p) (pw p k * (monus p one * monus p one)) :=
    le_mul_mono (one_le_of_pos hQ) (sq_pred_ge h3)
  have l₂ := le_mul_mono (le_refl (pw p k)) l₁
  have e := phi_ppow hp k
  refine le_congr ?_ ?_ l₂
  · exact (by ipra_ring : Γ ⊢[PRAAx] pw p k * (one * p) ≐ pw p k * p).eqTrans (pw_succ _ _).eqSymm
  · refine .eqTrans ?_ (congrMul e e).eqSymm
    ipra_ring

/-! ## `φ(n)² ≥ n` for odd `n` -/

/-- Read the positive cofactor and the totient product from the exact prime-power factorization. -/
theorem prime_power_totient_split {N p : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hp : Γ ⊢[PRAAx] prime p) :
    let P := pw p (val p N)
    let M := quo N P
    (Γ ⊢[PRAAx] M ≐ succ (pred M)) ∧ (Γ ⊢[PRAAx] N ≐ P * M) ∧
      (Γ ⊢[PRAAx] phi N ≐ phi P * phi M) := by
  have hp2 := hp.andE₁
  have e := cof_eq (m := N) hp2
  have hM := pos_of_eq_mul hN e
  have hP := pw_val_pos (m := N) hp2
  have cop := gcd_prime hp (cof_not_dvd hp2 hN)
  have hg := gcd_comm_one hP (coprime_pow hM (gcd_comm_one hM cop) (val p N))
  exact ⟨hM, e, (congrAp2 (sumF totBody) e e).eqTrans (Multiplicative.phi_mul_at hP hM hg)⟩

/-- Every right factor of an odd number is odd. -/
theorem odd_right_factor {N P M : PTm n} (h : Γ ⊢[PRAAx] N ≐ P * M)
    (hodd : Γ ⊢[PRAAx] rem N two ≐ one) : Γ ⊢[PRAAx] rem M two ≐ one := by
  refine eq_one_of_lt_two (rem_lt' two_pos' _) (.impI ?_)
  have d : ((rem M two ≐ zero) :: Γ) ⊢[PRAAx] dvd two N :=
    dvd_congr h.wk.eqSymm (dvd_congr (mul_comm _ _) (dvd_mul' two_pos' _ Prf.hyp0))
  exact succ_ne_zero' _ (a := zero) (hodd.wk.eqSymm.eqTrans d)

/-- `(n mod 2) · sg(n ∸ φ(n)²)`, over `0 = n`, `1 = x` (unused). -/
abbrev obB : PTm 2 := rem (var 0) two * sg (monus (var 0) (phi (var 0) * phi (var 0)))

theorem inst2_ob (N x : PTm n) : inst2 obB N x = rem N two * sg (monus N (phi N * phi N)) := by simp [inst2]

/-- The step for odd `n ≥ 1` with an odd prime divisor `p`. -/
theorem ob_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) (hodd : Γ ⊢[PRAAx] rem N two ≐ one)
    (hV : Γ ⊢[PRAAx] ap2 (sumF obB) N x ≐ zero) :
    Γ ⊢[PRAAx] le N (phi N * phi N) := by
  have hpo := prime_odd hp hpN hodd
  have h3 := three_le_of_odd_prime hp hpo
  obtain ⟨_, hNe, hmul⟩ := prime_power_totient_split hN hp
  have hmo := odd_right_factor hNe hodd
  -- The induction hypothesis at `m`.
  have h₀ := sum_zero_elim obB hV (cof_lt hN hp hpN)
  rw [inst2_ob] at h₀
  have ih : Γ ⊢[PRAAx] le (quo N (pw p (val p N))) (phi (quo N (pw p (val p N))) * phi (quo N (pw p (val p N)))) :=
    PhiDivides.sg_zero_inv ((one_mul _).eqSymm.eqTrans ((congrMul hmo.eqSymm (.eqRefl _)).eqTrans h₀))
  -- `φ(n) = φ(p^a) φ(m)` and `φ(p^a)² ≥ p^a`.
  have e₂ := congrAp2 powF (val_pos hN hp hpN).eqSymm (.eqRefl p)
  have hsq := le_congr e₂ (congrMul (congrAp2 (sumF totBody) e₂ e₂) (congrAp2 (sumF totBody) e₂ e₂))
    (ppow_sq hp h3 (pred (val p N)))
  have l := le_mul_mono hsq ih
  refine le_congr hNe.eqSymm ?_ l
  refine .eqTrans ?_ (congrMul hmul hmul).eqSymm
  ipra_ring

theorem ob_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF obB) N x ≐ zero) : Γ ⊢[PRAAx] inst2 obB N x ≐ zero := by
  rw [inst2_ob]
  refine .orE (zero_or_succ (rem N two)) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) ?_
  have hodd : ((rem N two ≐ succ (pred (rem N two))) :: Γ) ⊢[PRAAx] rem N two ≐ one :=
    eq_one_of_lt_two (rem_lt' two_pos' N) (.impI (succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans Prf.hyp0)))
  have hle : ((rem N two ≐ succ (pred (rem N two))) :: Γ) ⊢[PRAAx] le N (phi N * phi N) := by
    refine .orE (zero_or_succ N) ?_ ?_
    · exact (congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)
    refine .orE (zero_or_succ (pred N)) ?_ ?_
    · have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: (rem N two ≐ succ (pred (rem N two))) :: Γ) ⊢[PRAAx]
          N ≐ one := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have h1 := (congrAp2 (sumF totBody) e e).eqTrans EulerProduct.phi_one
      exact le_congr e.eqSymm ((one_mul _).eqSymm.eqTrans (congrMul h1 h1).eqSymm) (le_refl _)
    · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: (rem N two ≐ succ (pred (rem N two))) :: Γ)
          ⊢[PRAAx] N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact ob_found Prf.hyp1 (lpf_prime _) (dvd_congr e.eqSymm (Prf.andE₁ (lpf_dvd _))) hodd.wk.wk hV.wk.wk.wk
  exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hle)).eqTrans sg_zero)).eqTrans
    (mul_zero _)

private abbrev obF : Fm PTm 2 := ap2 (sumF obB) (var 0) (var 1) ≐ zero

private theorem ob₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] obF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · exact (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 (ob_step Prf.hyp0)).eqTrans (add_zero _))

/-- `φ(n)² ≥ n` for odd `n`. -/
theorem phi_sq_odd {N : PTm n} (hodd : Γ ⊢[PRAAx] rem N two ≐ one) : Γ ⊢[PRAAx] le N (phi N * phi N) := by
  have h := inst (Γ := Γ) ob₀ (![succ N, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim obB h ((succ_monus_succ _ _).eqTrans (le_refl N))
  rw [inst2_ob] at z
  exact PhiDivides.sg_zero_inv ((one_mul _).eqSymm.eqTrans ((congrMul hodd.eqSymm (.eqRefl _)).eqTrans z))

/-! ## `2 φ(n)² ≥ n` -/

/-- The cofactor of the exact power of two in a positive integer is odd. -/
theorem two_cofactor_odd {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] rem (quo N (pw two (val two N))) two ≐ one :=
  eq_one_of_lt_two (rem_lt' two_pos' _) (cof_not_dvd (le_refl two) hN)

/-- A positive integer with zero two-adic valuation is odd. -/
theorem odd_of_zero_two_valuation {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (h : Γ ⊢[PRAAx] val two N ≐ zero) : Γ ⊢[PRAAx] rem N two ≐ one := by
  have e := (cof_eq (m := N) (le_refl two)).eqTrans
    ((congrMul ((congrAp2 powF h (.eqRefl _)).eqTrans (pw_zero _)) (.eqRefl _)).eqTrans (one_mul _))
  exact (congrAp2 remF e (.eqRefl _)).eqTrans (two_cofactor_odd hN)

/-- Split an even positive integer and its totient using the same odd cofactor. -/
theorem two_adic_totient_split {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] val two N ≐ succ (pred (val two N))) :
    let M := quo N (pw two (val two N))
    let k := pred (val two N)
    (Γ ⊢[PRAAx] N ≐ pw two (succ k) * M) ∧ (Γ ⊢[PRAAx] phi N ≐ pw two k * phi M) ∧
      (Γ ⊢[PRAAx] rem M two ≐ one) ∧ (Γ ⊢[PRAAx] M ≐ succ (pred M)) := by
  obtain ⟨hM, e, ht⟩ := prime_power_totient_split hN prime_two
  have ep := congrAp2 powF ha (.eqRefl two)
  have hs : Γ ⊢[PRAAx] monus two one ≐ (one : PTm n) := (succ_monus_succ _ _).eqTrans (monus_zero _)
  have hv := (congrAp2 (sumF totBody) ep ep).eqTrans (phi_ppow prime_two (pred (val two N)))
  have hv' := hv.eqTrans ((congrMul (.eqRefl _) hs).eqTrans (Common.mul_one_right _))
  exact ⟨e.eqTrans (congrMul ep (.eqRefl _)), ht.eqTrans (congrMul hv' (.eqRefl _)), two_cofactor_odd hN, hM⟩

theorem le_two_mul (X : PTm n) : Γ ⊢[PRAAx] le X (two * X) :=
  le_of_eq_add (d := X) (by ipra_ring)

theorem phi_lower_pos {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] le N (two * (phi N * phi N)) := by
  refine .orE (zero_or_succ (val two N)) ?_ ?_
  · exact le_trans (phi_sq_odd (odd_of_zero_two_valuation hN.wk Prf.hyp0)) (le_two_mul _)
  · let Δ := (val two N ≐ succ (pred (val two N))) :: Γ
    obtain ⟨hNe, hφ, hmo, _⟩ := two_adic_totient_split (Γ := Δ) hN.wk Prf.hyp0
    let k := pred (val two N)
    let Q := pw two k
    let M := quo N (pw two (val two N))
    have hQ := one_le_of_pos (pw_pos' (two_pos' (Γ := Δ)) k)
    have b : Δ ⊢[PRAAx] le (one * Q) (Q * Q) := le_mul_mono hQ (le_refl Q)
    have l := le_mul_mono (le_refl two) (le_mul_mono b (phi_sq_odd hmo))
    have e := (congrMul (pw_succ two k) (.eqRefl M)).eqSymm.eqTrans hNe.eqSymm
    refine le_congr ?_ ?_ l
    · exact (by ipra_ring : Δ ⊢[PRAAx] two * (one * Q * M) ≐ Q * two * M).eqTrans e
    · exact (by ipra_ring : Δ ⊢[PRAAx] two * (Q * Q * (phi M * phi M)) ≐
        two * ((Q * phi M) * (Q * phi M))).eqTrans (congrMul (.eqRefl _) (congrMul hφ hφ)).eqSymm

/-- `thm:phi-lower` (first part) at an arbitrary `n`: `2 φ(n)² ≥ n`. -/
theorem phi_lower_at (N : PTm n) : Γ ⊢[PRAAx] le N (two * (phi N * phi N)) := by
  refine .orE (zero_or_succ N) ((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)) ?_
  exact phi_lower_pos Prf.hyp0

/-- `thm:phi-lower` (first part): `2 φ(n)² ≥ n`. -/
abbrev phiLowerFormula : Fm PTm 1 := le (var 0) (two * (phi (var 0) * phi (var 0)))

theorem phi_lower : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiLowerFormula :=
  closeUniv 1 (phi_lower_at (var 0))

/-- `φ(n)² ≥ n` for odd `n`. -/
abbrev phiSqOddFormula : Fm PTm 1 := (rem (var 0) two ≐ one) ⟶ le (var 0) (phi (var 0) * phi (var 0))

theorem phi_sq_odd_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiSqOddFormula :=
  closeUniv 1 (.impI (phi_sq_odd Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiLower

export_ipra AnalyticNumberTheory.PhiLower (le_mul_mono)
