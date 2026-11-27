import IPRADerivations.AnalyticNumberTheory.PhiDouble

/-!
# `φ(n M) = M φ(n)` when `M ∣ nᵗ`, and the power identity

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-power`:
`φ(n^k) = n^{k−1} φ(n)` for `n, k ≥ 1`.

No factorization is needed:

* `pow_point`: if `M ∣ nᵗ`, then `[gcd(k, nM) = 1] = [gcd(k, n) = 1]` (a common divisor `g` of `k`
  and `M` is coprime to `n`, hence to `nᵗ`, yet divides `nᵗ`);
* `per_sum`: `[gcd(k, n) = 1]` has period `n` (`PhiDouble.gcd_period`), so
  `∑_{k<nM} [gcd(k, n) = 1] = M φ(n)` by induction on `M` with `PhiDouble.sum_split`;
* `phi_mul_pow`: `M ∣ nᵗ → φ(nM) = M φ(n)`; with `M = n^{k−1}` this is `phi_power`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiPower

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot coprime_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (eqb_iff shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_eq' shift_mul' shift_rem')
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (cop_left)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (shiftBy inst2_shiftBy sum_split gcd_period)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Periodic sums -/

theorem per_step {N M : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ih : Γ ⊢[PRAAx] ap2 (sumF totBody) (N * M) N ≐ M * phi N) :
    Γ ⊢[PRAAx] ap2 (sumF totBody) (N * succ M) N ≐ succ M * phi N := by
  have e : Γ ⊢[PRAAx] N * succ M ≐ N + N * M := by ipra_ring
  have s₄ : Γ ⊢[PRAAx] ap2 (sumF (shiftBy totBody)) (N * M) N ≐ ap2 (sumF totBody) (N * M) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_shiftBy, inst2_tot, inst2_tot]
    exact congrEqb (gcd_period (shift_pos hN).wk _) (.eqRefl _)
  refine (congrAp2 (sumF totBody) e (.eqRefl _)).eqTrans ((sum_split totBody (N * M) N).eqTrans ?_)
  refine (congrAdd (.eqRefl _) (s₄.eqTrans ih)).eqTrans ?_
  ipra_ring

/-- Variables: `0 = M`, `1 = n`. -/
private abbrev perF : Fm PTm 2 :=
  (var 1 ≐ succ (pred (var 1))) ⟶ ap2 (sumF totBody) (var 1 * var 0) (var 1) ≐ var 0 * phi (var 1)

private theorem per₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] perF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2]
  · refine .impI ((congrAp2 (sumF totBody) (mul_zero _) (.eqRefl _)).eqTrans ((sum_zero _ _).eqTrans ?_))
    exact (zero_mul _).eqSymm
  · exact .impI (per_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `∑_{k<nM} [gcd(k, n) = 1] = M φ(n)`. -/
theorem per_sum {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF totBody) (N * M) N ≐ M * phi N := by
  have h := inst (Γ := Γ) per₀ (![M, N] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_mul, PTm.subst_pred, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ] at h
  exact .impE h hN

/-! ## The pointwise identity -/

section Point

variable {N M t : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
  (hd : Γ ⊢[PRAAx] dvd M (pw N t))
include hN hM hd

omit hN in
/-- `gcd(k, n) = 1 → gcd(k, M) = 1` when `M ∣ nᵗ`. -/
theorem cop_of_pow {k : PTm n} (h : Γ ⊢[PRAAx] gcd k N ≐ one) : Γ ⊢[PRAAx] gcd k M ≐ one := by
  have g := gcd_pos_right (a := k) hM
  have dg := gcd_dvd_at g
  have c₁ := coprime_dvd_left g (Prf.andE₁ dg) h
  have c₂ := coprime_pow g c₁ t
  have dp := dvd_trans' g hM (Prf.andE₂ dg) hd
  exact eq_one_of_dvd_one g (dvd_congr c₂ (gcd_greatest' g (dvd_self' g) dp))

/-- `[gcd(k, nM) = 1] = [gcd(k, n) = 1]` when `M ∣ nᵗ`. -/
theorem pow_point (k : PTm n) : Γ ⊢[PRAAx] eqb (gcd k (N * M)) one ≐ eqb (gcd k N) one := by
  refine eqb_iff (.impI (cop_left hN.wk Prf.hyp0)) (.impI ?_)
  exact Multiplicative.cop_both hN.wk hM.wk Prf.hyp0 (cop_of_pow hM.wk hd.wk Prf.hyp0)

/-- `φ(nM) = M φ(n)` when `M ∣ nᵗ`. -/
theorem phi_mul_pow_at : Γ ⊢[PRAAx] phi (N * M) ≐ M * phi N := by
  have hd' : Γ.map Fm.shift ⊢[PRAAx] dvd (Syn.shift M) (pw (Syn.shift N) (Syn.shift t)) := by
    have e := shift_eq' hd
    rw [shift_rem'] at e
    simpa [Syn.shift] using e
  refine (sum_congr_bounded totBody totBody (N * M) N (N * M) (.allI (.impI ?_))).eqTrans (per_sum hN M)
  rw [inst2_tot, inst2_tot, shift_mul']
  exact pow_point (shift_pos hN).wk (shift_pos hM).wk hd'.wk _

end Point

/-- `thm:phi-power` at arbitrary terms: `φ(n^{k+1}) = n^k φ(n)` for `n ≥ 1`. -/
theorem phi_power_at {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (k : PTm n) :
    Γ ⊢[PRAAx] phi (pw N (succ k)) ≐ pw N k * phi N := by
  have e : Γ ⊢[PRAAx] pw N (succ k) ≐ N * pw N k := (pw_succ _ _).eqTrans (mul_comm _ _)
  have hp : Γ ⊢[PRAAx] pw N k ≐ succ (pred (pw N k)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred ((congrAp2 powF (.eqRefl _) hN).eqTrans
      (DiophantineNumberTheory.FLTMultiples.pw_pos _ _))
  exact (congrAp2 (sumF totBody) e e).eqTrans (phi_mul_pow_at hN hp (t := k) (dvd_self' hp))

/-- `M ∣ nᵗ → φ(nM) = M φ(n)`; variables `0 = n − 1`, `1 = M − 1`, `2 = t`. -/
abbrev phiMulPowFormula : Fm PTm 3 :=
  dvd (succ (var 1)) (pw (succ (var 0)) (var 2)) ⟶
    phi (succ (var 0) * succ (var 1)) ≐ succ (var 1) * phi (succ (var 0))

theorem phi_mul_pow : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 phiMulPowFormula :=
  closeUniv 3 (.impI (phi_mul_pow_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm) Prf.hyp0))

/-- `thm:phi-power`: `φ(n^{k+1}) = n^k φ(n)`; variables `0 = n − 1`, `1 = k`. -/
abbrev phiPowerFormula : Fm PTm 2 :=
  phi (pw (succ (var 0)) (succ (var 1))) ≐ pw (succ (var 0)) (var 1) * phi (succ (var 0))

theorem phi_power : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 phiPowerFormula :=
  closeUniv 2 (phi_power_at (congrSucc (pred_succ _).eqSymm) (var 1))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiPower
