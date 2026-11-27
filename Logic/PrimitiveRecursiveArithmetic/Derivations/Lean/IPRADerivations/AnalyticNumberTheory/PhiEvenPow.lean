import IPRADerivations.AnalyticNumberTheory.Valuation

/-!
# `2^r ∣ φ(n)` for `r` distinct odd prime divisors

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-even`
(second part): if `n` has `r` distinct odd prime divisors, then `2^r ∣ φ(n)`.

The count is the explicit sum `r(n) = ∑_{q ≤ n} [q prime] [q ∣ n] (q mod 2)` (`oddR`).

* `peel_point`: for an odd prime `p`, `n = p^a m` with `a ≥ 1` and `p ∤ m`, every `q` has
  `o(q, n) = o(q, m) + [q = p]`, where `o` is the summand; hence `r(n) = r(m) + 1` (`r_peel`);
* `phi_ppow_even`: `2 ∣ φ(p^{k+1})` for an odd prime `p`;
* the theorem by strong induction on `n`, as the vanishing of a violation count: a counted `n`
  either has no odd prime divisor (`r(n) = 0`), or splits off one with `Valuation`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiEvenPow

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody coprime_pow totient_prime_power_at)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 inst2_lift3 at_pair shift_pair congrEqb rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq eqb_iff shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_eq' shift_mul' shift_rem')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The odd-prime count -/

/-- `[q prime] [q ∣ n] (q mod 2)`, over `0 = q`, `1 = n`. -/
abbrev oddB : PTm 2 := isP (var 0) * eqb (rem (var 1) (var 0)) zero * rem (var 0) two

/-- `r(n)`: the number of odd primes dividing `n`. -/
abbrev oddR (N : PTm n) : PTm n := ap2 (sumF oddB) (succ N) N

theorem inst2_odd (q N : PTm n) : inst2 oddB q N = isP q * eqb (rem N q) zero * rem q two := by
  simp [inst2]

theorem isP_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] isP a ≐ isP b :=
  congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus h (.eqRefl _))))
    (congrEqb (lpf_congr h) h)

/-! ## Peeling an odd prime -/

section Peel

variable {p a m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] rem p two ≐ one)
  (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hrm : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p)))
include hp hodd ha hrm

omit hodd hrm in
theorem p_dvd_n : Γ ⊢[PRAAx] rem (pw p a * m) p ≐ zero := by
  refine dvd_of_eq' (prime_eq_succ_pred hp) (w := pw p (pred a) * m) ?_
  have e₁ := natEq ((congrAp2 powF ha (.eqRefl p)).eqTrans (pw_succ p (pred a)))
  apply deriveNat; ipra_simps; rw [e₁]; ring

theorem peel_eq {q : PTm n} (hqp : Γ ⊢[PRAAx] q ≐ p) (hI : Γ ⊢[PRAAx] isP q ≐ one) :
    Γ ⊢[PRAAx] isP q * eqb (rem (pw p a * m) q) zero * rem q two ≐
      isP q * eqb (rem m q) zero * rem q two + eqb q p := by
  have hDn := eqb_of_eq ((congrAp2 remF (.eqRefl _) hqp).eqTrans (p_dvd_n (m := m) hp ha))
  have hO := (congrAp2 remF hqp (.eqRefl _)).eqTrans hodd
  have hDm : Γ ⊢[PRAAx] eqb (rem m q) zero ≐ zero :=
    eqb_of_ne (.impI (succ_ne_zero' _ (hrm.wk.eqSymm.eqTrans
      ((congrAp2 remF (.eqRefl _) hqp.wk).eqSymm.eqTrans Prf.hyp0))))
  have hE := eqb_of_eq hqp
  ipra_lc Groth.ι (Q.mk _ (eqb (rem (pw p a * m) q) zero)) * Groth.ι (Q.mk _ (rem q two)) * natEq hI +
    Groth.ι (Q.mk _ (rem q two)) * natEq hDn + natEq hO -
    Groth.ι (Q.mk _ (sg (monus q one))) * Groth.ι (Q.mk _ (eqb (lpf q) q)) * Groth.ι (Q.mk _ (rem q two)) * natEq hDm -
    natEq hE

omit hodd hrm in
theorem peel_ne {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hne : Γ ⊢[PRAAx] neg (q ≐ p)) :
    Γ ⊢[PRAAx] isP q * eqb (rem (pw p a * m) q) zero * rem q two ≐
      isP q * eqb (rem m q) zero * rem q two + eqb q p := by
  have hq1 := prime_eq_succ_pred hq
  have gq := coprime_pow hq1 (gcd_distinct_primes hq hp hne) a
  have hD : Γ ⊢[PRAAx] eqb (rem (pw p a * m) q) zero ≐ eqb (rem m q) zero := by
    refine eqb_iff (.impI (gauss hq1.wk gq.wk Prf.hyp0)) (.impI ?_)
    exact dvd_congr (mul_comm _ _) (dvd_mul' hq1.wk (pw p a) Prf.hyp0)
  exact (congrMul (congrMul (.eqRefl _) hD) (.eqRefl _)).eqTrans
    ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) (eqb_of_ne hne).eqSymm))

theorem peel_point (q : PTm n) :
    Γ ⊢[PRAAx] inst2 oddB q (pw p a * m) ≐ inst2 oddB q m + eqb q p := by
  rw [inst2_odd, inst2_odd]
  refine .orE (isP_01 q) ?_ ?_
  · -- `q` is not prime, so `q ≠ p`.
    have hI : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    have hE : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] eqb q p ≐ zero := by
      refine eqb_of_ne (.impI (succ_ne_zero' _ (a := zero) ?_))
      exact (isP_of_prime hp.wk.wk).eqSymm.eqTrans ((isP_congr Prf.hyp0).eqSymm.eqTrans hI.wk)
    ipra_lc (Groth.ι (Q.mk _ (eqb (rem (pw p a * m) q) zero)) * Groth.ι (Q.mk _ (rem q two)) - Groth.ι (Q.mk _ (eqb (rem m q) zero)) * Groth.ι (Q.mk _ (rem q two))) * natEq hI -
      natEq hE
  · have hI : ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    refine .orE (eq_or_ne q p) ?_ ?_
    · exact peel_eq hp.wk.wk hodd.wk.wk ha.wk.wk hrm.wk.wk Prf.hyp0 hI.wk
    · exact peel_ne hp.wk.wk ha.wk.wk (prime_of_isP hI).wk Prf.hyp0

end Peel

/-! ## Extending the bound -/

theorem odd_far {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] inst2 oddB (succ m + k) m ≐ zero := by
  rw [inst2_odd]
  have hQ : Γ ⊢[PRAAx] succ m + k ≐ succ (pred (succ m + k)) :=
    eq_succ_pred (y := m + k) (by ipra_ring)
  have hr := rem_eq' hQ (z := m) (q := zero) (r := m) (by ipra_ring)
    (le_of_eq_add (d := k) (by apply deriveNat; ipra_simps))
  have he : Γ ⊢[PRAAx] eqb (rem m (succ m + k)) zero ≐ zero :=
    (congrEqb hr (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (hm.wk.eqSymm.eqTrans Prf.hyp0))))
  refine (congrMul (congrMul (.eqRefl _) he) (.eqRefl _)).eqTrans ?_
  ipra_ring

theorem sum_extend {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF oddB) (succ m + k) m ≐ ap2 (sumF oddB) (succ m) m := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF oddB) (succ (Syn.shift m) + var 0) (Syn.shift m) ≐
      ap2 (sumF oddB) (succ (Syn.shift m)) (Syn.shift m)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact congrAp2 (sumF oddB) (add_zero _) (.eqRefl _)
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, Syn.subst_shift,
        Syn.repl_succ, subst_repl_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      refine (congrAp2 (sumF oddB) (add_succ _ _) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
      exact (congrAdd Prf.hyp0 (odd_far (shift_pos hm).wk _)).eqTrans (add_zero _)
  have h := Prf.allE k hall
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

/-! ## `r(p^a m) = r(m) + 1` -/

/-- `o(q, m) + [q = p]`, over `0 = q`, `1 = p`, `2 = m`. -/
abbrev F3 : PTm 3 := Syn.subst ![var 0, var 2] oddB

theorem inst3_F3 (q p m : PTm n) : inst3 F3 q p m = inst2 oddB q m := by
  simp only [inst3, inst2, F3, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

theorem shift_pw' (a b : PTm n) : Syn.shift (pw a b) = pw (Syn.shift a) (Syn.shift b) := by simp [Syn.shift]

theorem shift_odd {p : PTm n} (h : Γ ⊢[PRAAx] rem p two ≐ one) :
    Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift p) two ≐ one := by
  simpa [Syn.shift] using shift_eq' h

theorem shift_rpos {m p : PTm n} (h : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p))) :
    Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift m) (Syn.shift p) ≐ succ (pred (rem (Syn.shift m) (Syn.shift p))) := by
  simpa [Syn.shift] using shift_eq' h

section R

variable {p a m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] rem p two ≐ one)
  (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hrm : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p)))
  (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
include hp hodd ha hrm hm

theorem r_peel : Γ ⊢[PRAAx] oddR (pw p a * m) ≐ oddR m + one := by
  have hP := pw_pos' (prime_eq_succ_pred hp) a
  have hn := pos_mul hP hm
  have s₁ : Γ ⊢[PRAAx] ap2 (sumF oddB) (succ (pw p a * m)) (pw p a * m) ≐
      ap2 (sumF (addBody (lift3 F3) (lift3 indBody))) (succ (pw p a * m)) (pairT p m) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pair, inst2_addBody, inst2_lift3, inst2_lift3]
    refine .eqTrans ?_ (congrAdd (congrInst3 _ (.eqRefl _) (fst_pair _ _).eqSymm (snd_pair _ _).eqSymm)
      (congrInst3 _ (.eqRefl _) (fst_pair _ _).eqSymm (snd_pair _ _).eqSymm))
    rw [inst3_F3]
    have e : inst3 indBody (var 0 : PTm (n + 1)) (Syn.shift p) (Syn.shift m) = eqb (var 0) (Syn.shift p) := by
      simp [inst3]
    rw [e, shift_mul', shift_pw']
    exact peel_point (prime_shift hp).wk (shift_odd hodd).wk (shift_pos ha).wk (shift_rpos hrm).wk _
  have s₂ := sum_add (Γ := Γ) (lift3 F3) (lift3 indBody) (succ (pw p a * m)) (pairT p m)
  have s₃ : Γ ⊢[PRAAx] ap2 (sumF (lift3 F3)) (succ (pw p a * m)) (pairT p m) ≐
      ap2 (sumF oddB) (succ (pw p a * m)) m := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pair]
    exact (at_pair F3 _ _ _).eqTrans (by rw [inst3_F3]; exact .eqRefl _)
  have e : Γ ⊢[PRAAx] succ (pw p a * m) ≐ succ m + pred (pw p a) * m := by
    ipra_lc Groth.ι (Q.mk _ m) * natEq hP
  have s₄ := (congrAp2 (sumF oddB) e (.eqRefl m)).eqTrans (sum_extend hm _)
  have hlt : Γ ⊢[PRAAx] lt p (succ (pw p a * m)) :=
    (succ_monus_succ _ _).eqTrans (dvd_le' (prime_eq_succ_pred hp) (p_dvd_n (m := m) hp ha) hn)
  have s₅ := (sum2_lift indBody (succ (pw p a * m)) p m).eqSymm.eqTrans (sum2_delta hlt)
  exact s₁.eqTrans (s₂.eqTrans (congrAdd (s₃.eqTrans s₄) s₅))

end R

/-! ## The local factor -/

theorem two_pos'' : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-- `2 ∣ φ(p^{k+1})` for an odd prime `p`. -/
theorem phi_ppow_even {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] rem p two ≐ one) (k : PTm n) :
    Γ ⊢[PRAAx] dvd two (phi (pw p (succ k))) := by
  refine dvd_of_eq' two_pos'' (w := pw p k * quo p two) ?_
  ipra_lc natEq (totient_prime_power_at (k := k) hp) + natEq (pw_succ p k) +
    Groth.ι (Q.mk _ (pw p k)) * natEq (div_eq (j := p) two_pos'') + Groth.ι (Q.mk _ (pw p k)) * natEq hodd

/-! ## Finding an odd prime divisor -/

/-- `[o(q, n) = 0]`, over `0 = q`, `1 = n`. -/
abbrev findB : PTm 2 := eqb oddB zero

theorem inst2_find (q N : PTm n) : inst2 findB q N = eqb (inst2 oddB q N) zero := by simp [inst2]

/-- The first `q ≤ n` with `o(q, n) ≠ 0`, or `n + 1`. -/
abbrev wit (N : PTm n) : PTm n := Search.mu findB (succ N) N

theorem ne_zero_left {x y : PTm n} (h : Γ ⊢[PRAAx] neg (x * y ≐ zero)) : Γ ⊢[PRAAx] neg (x ≐ zero) :=
  .impI (.impE h.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))

theorem ne_zero_right {x y : PTm n} (h : Γ ⊢[PRAAx] neg (x * y ≐ zero)) : Γ ⊢[PRAAx] neg (y ≐ zero) :=
  .impI (.impE h.wk ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

/-- `x < 2` and `x ≠ 0` give `x = 1`. -/
theorem eq_one_of_lt_two {x : PTm n} (h₁ : Γ ⊢[PRAAx] lt x two) (h₂ : Γ ⊢[PRAAx] neg (x ≐ zero)) :
    Γ ⊢[PRAAx] x ≐ one := by
  refine .orE (zero_or_succ x) (.botE _ (.impE h₂.wk Prf.hyp0)) ?_
  exact le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans h₁.wk) (one_le_of_pos Prf.hyp0)

/-- A found witness is an odd prime divisor. -/
theorem wit_spec {N : PTm n} (hlt : Γ ⊢[PRAAx] lt (wit N) (succ N)) :
    Γ ⊢[PRAAx] prime (wit N) ⋏ ((rem (wit N) two ≐ one) ⋏ dvd (wit N) N) := by
  have hf := Prf.impE (Prf.andE₁ (Prf.andE₂ (Search.search_spec (Γ := Γ) (f := findB) (succ N) zero N))) hlt
  rw [inst2_find, inst2_odd] at hf
  have h := ne_of_eqb_zero hf
  have h₁ := ne_zero_left h
  have hO := ne_zero_right h
  have hP := ne_zero_left h₁
  have hD := ne_zero_right h₁
  refine .andI ?_ (.andI ?_ ?_)
  · refine .orE (isP_01 (wit N)) (.botE _ (.impE hP.wk Prf.hyp0)) ?_
    exact prime_of_isP Prf.hyp0
  · exact eq_one_of_lt_two (rem_lt' two_pos'' _) hO
  · exact eq_of_eqb_ne hD

/-- Without a witness, `r(n) = 0`. -/
theorem r_zero_of_none {N : PTm n} (hle : Γ ⊢[PRAAx] le (succ N) (wit N)) : Γ ⊢[PRAAx] oddR N ≐ zero := by
  have hle' : Γ.map Fm.shift ⊢[PRAAx] le (succ (Syn.shift N)) (wit (Syn.shift N)) := by
    have h := shift_eq' hle
    simp [Syn.shift] at h
    exact h
  have e : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  refine sum_zero_of_bounded oddB N (succ N) ?_
  rw [e]
  refine .allI (.impI ?_)
  have hlt : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (wit (Syn.shift N)) :=
    le_trans Prf.hyp0 hle'.wk
  have hne := Search.search_minimal (f := findB) hlt
  rw [inst2_find] at hne
  exact eq_of_eqb_ne hne

/-! ## Strong induction -/

/-- `sg(φ(N) mod 2^{r(N)})`, over `0 = N`, `1 = x` (unused). -/
abbrev evB : PTm 2 := sg (rem (phi (var 0)) (pw two (oddR (var 0))))

theorem inst2_ev (N x : PTm n) : inst2 evB N x = sg (rem (phi N) (pw two (oddR N))) := by simp [inst2]

/-- The step when `n` has an odd prime divisor `p`. -/
theorem ev_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hodd : Γ ⊢[PRAAx] rem p two ≐ one) (hpN : Γ ⊢[PRAAx] dvd p N)
    (hV : Γ ⊢[PRAAx] ap2 (sumF evB) N x ≐ zero) :
    Γ ⊢[PRAAx] dvd (pw two (oddR N)) (phi N) := by
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  have ha := val_eq_succ_pred_of_dvd hp2 hN hpN
  have hP := pw_val_pos (m := N) hp2
  have hNe := cof_eq (m := N) hp2
  have hrm := cof_rem_eq_succ_pred hp2 hN
  have hm := cof_eq_succ_pred hp2 hN
  have hlt := cof_lt_of_dvd hp2 hN hpN
  -- The induction hypothesis at `m`.
  have h₀ := sum_zero_elim evB hV hlt
  rw [inst2_ev] at h₀
  have dm := PhiDivides.sg_zero_inv h₀
  -- `φ(n) = φ(p^a) φ(m)` with `2 ∣ φ(p^a)`, and `r(n) = r(m) + 1`.
  have g₁ := gcd_prime hp (.impI (succ_ne_zero' _ (hrm.wk.eqSymm.eqTrans Prf.hyp0)))
  have hg := gcd_comm_one hP (coprime_pow hm (gcd_comm_one hm g₁) (val p N))
  have hmul := Multiplicative.phi_mul_at hP hm hg
  have e₂ : Γ ⊢[PRAAx] pw p (succ (pred (val p N))) ≐ pw p (val p N) := congrAp2 powF ha.eqSymm (.eqRefl _)
  have heven := dvd_congr (congrAp2 (sumF totBody) e₂ e₂) (phi_ppow_even hp hodd (pred (val p N)))
  have hr := r_peel hp hodd ha hrm hm
  have eP := eq_of_dvd' two_pos'' heven
  have em := eq_of_dvd' (pw_pos' two_pos'' _) dm
  have ep : Γ ⊢[PRAAx] pw two (oddR (quo N (pw p (val p N))) + one) ≐ pw two (oddR (quo N (pw p (val p N)))) * two :=
    (congrAp2 powF (by ipra_ring) (.eqRefl two)).eqTrans (pw_succ _ _)
  have hd : Γ ⊢[PRAAx] dvd (pw two (oddR (quo N (pw p (val p N))) + one))
      (phi (pw p (val p N)) * phi (quo N (pw p (val p N)))) := by
    refine dvd_of_eq' (pw_pos' two_pos'' _) (w := quo (phi (pw p (val p N))) two *
      quo (phi (quo N (pw p (val p N)))) (pw two (oddR (quo N (pw p (val p N)))))) ?_
    refine (congrMul eP em).eqTrans (.eqTrans ?_ (congrMul ep.eqSymm (.eqRefl _)))
    ipra_ring
  have hφ := (congrAp2 (sumF totBody) hNe hNe).eqTrans hmul
  have hR := (congrAp2 (sumF oddB) (congrSucc hNe) hNe).eqTrans hr
  exact dvd_congr_left (congrAp2 powF hR.eqSymm (.eqRefl _)) (dvd_congr hφ.eqSymm hd)

/-- The step: `2^{r(n)} ∣ φ(n)`, given the claim below `n`. -/
theorem ev_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF evB) N x ≐ zero) :
    Γ ⊢[PRAAx] dvd (pw two (oddR N)) (phi N) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have h0 : ((N ≐ zero) :: Γ) ⊢[PRAAx] phi N ≐ zero :=
      (congrAp2 (sumF totBody) Prf.hyp0 Prf.hyp0).eqTrans (sum_zero _ _)
    exact (congrAp2 remF h0 (.eqRefl _)).eqTrans (rem_zero _)
  · have hN : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    refine .orE (lt_or_le (wit N) (succ N)) ?_ ?_
    · have ws := wit_spec (Prf.hyp0 : (lt (wit N) (succ N) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] _)
      exact ev_found hN.wk (Prf.andE₁ ws) (Prf.andE₁ (Prf.andE₂ ws)) (Prf.andE₂ (Prf.andE₂ ws)) hV.wk.wk
    · have hr0 := r_zero_of_none (Prf.hyp0 : (le (succ N) (wit N) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] _)
      exact (congrAp2 remF (.eqRefl _) ((congrAp2 powF hr0 (.eqRefl _)).eqTrans (pw_zero _))).eqTrans (rem_one _)

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev evF : Fm PTm 2 := ap2 (sumF evB) (var 0) (var 1) ≐ zero

private theorem ev₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] evF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_ev]
    exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (ev_step Prf.hyp0))).eqTrans sg_zero

/-- `thm:phi-even` (second part) at an arbitrary `n`: `2^{r(n)} ∣ φ(n)`. -/
theorem phi_even_pow_at (N : PTm n) : Γ ⊢[PRAAx] dvd (pw two (oddR N)) (phi N) := by
  have h := inst (Γ := Γ) ev₀ (![succ N, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim_last evB h
  rw [inst2_ev] at z
  exact PhiDivides.sg_zero_inv z

/-- `thm:phi-even` (second part): `2^{r(n)} ∣ φ(n)`, with `r(n)` the number of odd primes
dividing `n`. -/
abbrev phiEvenPowFormula : Fm PTm 1 := dvd (pw two (oddR (var 0))) (phi (var 0))

theorem phi_even_pow : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiEvenPowFormula :=
  closeUniv 1 (phi_even_pow_at (var 0))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiEvenPow

export_ipra AnalyticNumberTheory.PhiEvenPow (eq_one_of_lt_two)
