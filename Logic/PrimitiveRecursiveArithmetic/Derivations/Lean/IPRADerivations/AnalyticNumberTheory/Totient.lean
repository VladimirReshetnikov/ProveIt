import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Euler's totient at prime powers

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Definition
`def:totient` and Theorem `thm:phi-prime-power`.

`φ(n) = ∑_{a<n} [gcd(a, n) = 1]`. For a prime `p` and `k ≥ 0`:

`φ(p^{k+1}) + p^k = p^{k+1}`, so `φ(p) = p - 1` and `φ(p^a) = p^a - p^{a-1}` (`totient_prime_power`).

* For every `j`, `[gcd(j, p^{k+1}) = 1] + [p ∣ j] = 1` (`indicator_sum`): a common divisor
  argument in one direction, and `coprime_pow` (coprimality to `p` passes to its powers)
  in the other.
* `∑_{t<j} [p ∣ t] = ⌈j/p⌉ = (j + p − 1) / p` (`count_multiples`), by induction on `j`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Totient

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift subst_prime)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[gcd(a, n) = 1]`, over `0 = a`, `1 = n`. -/
abbrev totBody : PTm 2 := eqb (gcd (var 0) (var 1)) one
/-- `φ(n)`. -/
abbrev phi (N : PTm n) : PTm n := ap2 (sumF totBody) N N
/-- `[p ∣ t]`, over `0 = t`, `1 = p`. -/
abbrev mulBody : PTm 2 := eqb (rem (var 0) (var 1)) zero

theorem inst2_tot (a x : PTm n) : inst2 totBody a x = eqb (gcd a x) one := by
  simp only [inst2, subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
theorem inst2_mul (a x : PTm n) : inst2 mulBody a x = eqb (rem a x) zero := by simp [inst2]

/-! ## Coprimality to powers -/

theorem coprime_pow {j p : PTm n} (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) (h : Γ ⊢[PRAAx] gcd j p ≐ one)
    (m : PTm n) : Γ ⊢[PRAAx] gcd j (pw p m) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (gcd (Syn.shift j) (pw (Syn.shift p) (var 0)) ≐ one) := by
    ipra_qfind (trivial) [subst_ex2, subst_ap2]
    · have hd := gcd_pos (B := pw p zero) hj
      have hdd := gcd_dvd' (b := pw p zero) hj
      exact eq_one_of_dvd_one hd (dvd_congr (pw_zero _) (Prf.andE₂ hdd))
    · have hj' := Common.pos_shift hj
      have h' := Gcd.shift_coprime h
      have c := coprime_mul (c := pw (Syn.shift p) (var 0)) (c' := Syn.shift p) hj'.wk Prf.hyp0 h'.wk
      have hd := gcd_pos (Γ := (gcd (Syn.shift j) (pw (Syn.shift p) (var 0)) ≐ one) :: Γ.map Fm.shift)
        (B := pw (Syn.shift p) (succ (var 0))) hj'.wk
      have hdd := gcd_dvd' (Γ := (gcd (Syn.shift j) (pw (Syn.shift p) (var 0)) ≐ one) :: Γ.map Fm.shift)
        (b := pw (Syn.shift p) (succ (var 0))) hj'.wk
      refine eq_one_of_dvd_one hd (dvd_congr c (gcd_greatest' hd (Prf.andE₁ hdd) ?_))
      exact dvd_congr (pw_succ _ _) (Prf.andE₂ hdd)
  have h2 := Prf.allE m hall
  simp only [Fm.subst_eq, subst_ex2, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-! ## The indicators -/

/-- `[gcd(j, p^{k+1}) = 1] + [p ∣ j] = 1` for a prime `p`. -/
theorem indicator_sum {p j k : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] eqb (gcd j (pw p (succ k))) one + eqb (rem j p) zero ≐ one := by
  have hq := prime_eq_succ_pred hp
  have hp2 : Γ ⊢[PRAAx] le two p := by unfold prime at hp; exact Prf.andE₁ hp
  refine .orE (eq_or_ne (rem j p) zero) ?_ ?_
  · have e₁ := eqb_of_eq (Prf.hyp0 : ((rem j p ≐ zero) :: Γ) ⊢[PRAAx] rem j p ≐ zero)
    have hne : ((rem j p ≐ zero) :: Γ) ⊢[PRAAx] neg (gcd j (pw p (succ k)) ≐ one) := by
      refine .impI ?_
      have dpP := dvd_of_eq' (Γ := (gcd j (pw p (succ k)) ≐ one) :: (rem j p ≐ zero) :: Γ) hq.wk.wk
        (w := pw p k) ((pw_succ p k).eqTrans (mul_comm _ _))
      have d := gcd_greatest' hq.wk.wk (Prf.hyp1 : ((gcd j (pw p (succ k)) ≐ one) :: (rem j p ≐ zero) :: Γ)
        ⊢[PRAAx] dvd p j) dpP
      have p1 := eq_one_of_dvd_one hq.wk.wk (dvd_congr Prf.hyp0 d)
      exact lt_irrefl one _ (le_congr (.eqRefl _) p1 hp2.wk.wk)
    exact (congrAdd (eqb_of_ne hne) e₁).eqTrans (zero_add _)
  · have e₁ := eqb_of_ne (Prf.hyp0 : (neg (rem j p ≐ zero) :: Γ) ⊢[PRAAx] neg (rem j p ≐ zero))
    have hj : (neg (rem j p ≐ zero) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := by
      refine .orE (zero_or_succ j) ?_ Prf.hyp0
      exact .botE _ (.impE Prf.hyp1 ((congrAp2 remF Prf.hyp0 (.eqRefl _)).eqTrans (rem_zero _)))
    have g₁ := gcd_prime hp.wk (Prf.hyp0 : (neg (rem j p ≐ zero) :: Γ) ⊢[PRAAx] neg (dvd p j))
    have g₃ := coprime_pow hj (gcd_comm_one hj g₁) (succ k)
    exact (congrAdd (eqb_of_eq g₃) e₁).eqTrans (add_zero _)

/-! ## Counting multiples -/

theorem quo_eq {z q r M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hz : Γ ⊢[PRAAx] z ≐ M * q + r)
    (hr : Γ ⊢[PRAAx] lt r M) : Γ ⊢[PRAAx] quo z M ≐ q :=
  Prf.andE₁ (div_mod_unique_at hM hz hr)

alias pred_lt := Common.pred_lt

/-- Adding the positive divisor to a dividend increases the quotient in its decomposition by one. -/
theorem succ_add_of_div_eq {x p q r e : PTm n} (hx : Γ ⊢[PRAAx] x ≐ p * q + r)
    (hp : Γ ⊢[PRAAx] p ≐ succ e) :
    Γ ⊢[PRAAx] succ x + e ≐ p * succ q + r := by
  ipra_lc natEq hx - natEq hp

private theorem quo_succ_add_pred {x p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] quo (succ x + pred p) p ≐ succ (quo x p) := by
  have d := div_mod_at (x := x) hp
  exact quo_eq hp (succ_add_of_div_eq (Prf.andE₁ d) hp) (Prf.andE₂ d)

/-- `⌈(j+1)/p⌉ = ⌈j/p⌉ + [p ∣ j]`. -/
theorem quo_step {j p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] quo (succ j + pred p) p ≐ quo (j + pred p) p + eqb (rem j p) zero :=
by
  have d := div_mod_at (x := j) hp
  have ej := Prf.andE₁ d
  have hr := Prf.andE₂ d
  refine .orE (zero_or_succ (rem j p)) ?_ ?_
  · let Δ : List (Fm PTm n) := (rem j p ≐ zero) :: Γ
    have hR : Δ ⊢[PRAAx] rem j p ≐ zero := Prf.hyp0
    have q : Δ ⊢[PRAAx] quo (j + pred p) p ≐ quo j p :=
      quo_eq hp.wk (r := pred p) (by ipra_lc natEq ej.wk + natEq hR) (pred_lt hp.wk)
    exact (quo_succ_add_pred hp.wk).eqTrans (by ipra_lc -natEq q - natEq (eqb_of_eq hR))
  · let Δ : List (Fm PTm n) := (rem j p ≐ succ (pred (rem j p))) :: Γ
    have hR : Δ ⊢[PRAAx] rem j p ≐ succ (pred (rem j p)) := Prf.hyp0
    have hne : Δ ⊢[PRAAx] neg (rem j p ≐ zero) :=
      .impI (succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))
    have q : Δ ⊢[PRAAx] quo (j + pred p) p ≐ succ (quo j p) :=
      quo_eq hp.wk (r := pred (rem j p))
        (by ipra_lc natEq ej.wk + natEq hR - natEq hp.wk)
        (lt_of_le_of_lt (le_congr (.eqRefl _) hR.eqSymm (le_succ_self _)) hr.wk)
    exact (quo_succ_add_pred hp.wk).eqTrans (by ipra_lc -natEq q - natEq (eqb_of_ne hne))

/-- Variables: `0 = j`, `1 = p`. -/
private abbrev countF : Fm PTm 2 :=
  (var 1 ≐ succ (pred (var 1))) ⟶ ap2 (sumF mulBody) (var 0) (var 1) ≐ quo (var 0 + pred (var 1)) (var 1)

private theorem count₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] countF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2]
  · refine .impI ((sum_zero _ _).eqTrans (quo_eq (q := zero) (r := pred (var 0)) Prf.hyp0 ?_ (pred_lt Prf.hyp0)).eqSymm)
    ipra_ring
  · refine .impI ?_
    refine (sum_succ' _ (var 0) (var 1)).eqTrans ?_
    rw [inst2_mul]
    exact (congrAdd (.impE Prf.hyp1 Prf.hyp0) (.eqRefl _)).eqTrans (quo_step Prf.hyp0).eqSymm

theorem count_multiples {j p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] ap2 (sumF mulBody) j p ≐ quo (j + pred p) p := by
  have h := inst (Γ := Γ) count₀ (![j, p] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_pred, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ] at h
  exact .impE h hp

/-- The count of multiples of positive `p` in `[0, x]` is `⌊x/p⌋ + 1`. -/
theorem count_multiples_succ {x p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] ap2 (sumF mulBody) (succ x) p ≐ succ (quo x p) :=
  (count_multiples (j := succ x) hp).eqTrans (quo_succ_add_pred hp)

/-! ## The theorem -/

theorem totient_prime_power_at {p k : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] phi (pw p (succ k)) + pw p k ≐ pw p (succ k) := by
  have hq := prime_eq_succ_pred hp
  -- `∑_{j<N} [gcd(j, P) = 1] + ∑_{j<N} [p ∣ j] = N` for every `N`.
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF totBody) (var 0) (pw (Syn.shift p) (succ (Syn.shift k))) +
      ap2 (sumF mulBody) (var 0) (Syn.shift p) ≐ var 0) := by
    ipra_qfind (trivial) [subst_ap2]
    · exact (congrAdd (sum_zero _ _) (sum_zero _ _)).eqTrans (add_zero _)
    · have hp' := (prime_shift hp).wk (ψ := ap2 (sumF totBody) (var 0) (pw (Syn.shift p) (succ (Syn.shift k))) +
        ap2 (sumF mulBody) (var 0) (Syn.shift p) ≐ var 0)
      have ind := indicator_sum (j := var 0) (k := Syn.shift k) hp'
      have e₁ := sum_succ' (Γ := (ap2 (sumF totBody) (var 0) (pw (Syn.shift p) (succ (Syn.shift k))) +
        ap2 (sumF mulBody) (var 0) (Syn.shift p) ≐ var 0) :: Γ.map Fm.shift) totBody (var 0)
        (pw (Syn.shift p) (succ (Syn.shift k)))
      have e₂ := sum_succ' (Γ := (ap2 (sumF totBody) (var 0) (pw (Syn.shift p) (succ (Syn.shift k))) +
        ap2 (sumF mulBody) (var 0) (Syn.shift p) ≐ var 0) :: Γ.map Fm.shift) mulBody (var 0) (Syn.shift p)
      rw [inst2_tot] at e₁
      rw [inst2_mul] at e₂
      ipra_lc natEq e₁ + natEq e₂ + natEq ind +
        natEq (Prf.hyp0 : ((ap2 (sumF totBody) (var 0) (pw (Syn.shift p) (succ (Syn.shift k))) + ap2 (sumF mulBody) (var 0) (Syn.shift p) ≐ var 0) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  have h := Prf.allE (pw p (succ k)) hall
  simp only [Fm.subst_eq, PTm.subst_add, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] at h
  -- `∑_{j<p^{k+1}} [p ∣ j] = p^k`.
  have c := (count_multiples (j := pw p (succ k)) hq).eqTrans (quo_eq (q := pw p k) (r := pred p) hq
    ((congrAdd ((pw_succ p k).eqTrans (mul_comm _ _)) (.eqRefl _))) (pred_lt hq))
  exact (congrAdd (.eqRefl _) c.eqSymm).eqTrans h

/-- `thm:phi-prime-power`: `φ(p^{k+1}) + p^k = p^{k+1}`; variables `0 = p`, `1 = k`. -/
abbrev totientFormula : Fm PTm 2 :=
  prime (var 0) ⟶ phi (pw (var 0) (succ (var 1))) + pw (var 0) (var 1) ≐ pw (var 0) (succ (var 1))

theorem totient_prime_power : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 totientFormula :=
  closeUniv 2 (.impI (totient_prime_power_at Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.Totient

export_ipra AnalyticNumberTheory.Totient (coprime_pow count_multiples inst2_tot mulBody pred_lt quo_eq totBody
  totient_prime_power_at)
