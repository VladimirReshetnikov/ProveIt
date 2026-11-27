import IPRADerivations.AnalyticNumberTheory.FactorVector

/-!
# The Möbius function and Möbius cancellation

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Lemma `lem:mobius-cancel`.

With a prime bound `N` (any `N` above the argument), the number of prime divisors and the number of
primes whose square divides `x` are bounded sums over valuations:
`ω_N(x) = ∑_{q<N} [q prime] sg(v_q(x))`, `s_N(x) = ∑_{q<N} [q prime] sg(v_q(x) ∸ 1)`.
The Möbius function is the signed pair `μ(x) = μ⁺(x) − μ⁻(x)` with
`μ⁺ = [s = 0][ω even]` and `μ⁻ = [s = 0][ω odd]`.

Multiplying by a prime `p < N` changes the valuations only at `p`
(`v_q(a p) = v_q(a) + [q = p]`, `val_mul_prime`), so:

* `swap`: for `p ∤ a`, `μ⁺(a p) = μ⁻(a)` and `μ⁻(a p) = μ⁺(a)` (`ω` grows by one, `s` is unchanged);
* `kill`: for `p ∣ a`, `μ⁺(a p) = μ⁻(a p) = 0` (`p² ∣ a p`).

The divisor sums `∑_{d ∣ m} μ^±(d)` are `∑_{d ≤ m} [d ≥ 1][d ∣ m] μ^±_{m+1}(d)`. With `p = ℓ(m)`:

* `split_reindex`: split by `[p ∣ d]`, extend the multiple part to the bound `(m + 1) + (p − 1) m`,
  and reindex it by `d = a p` (`GcdFiber.reindex`); `mult_pt` gives
  `[a p ∣ m] μ^±(a p) = [p ∤ a][a ∣ m] μ^∓(a)` (by `swap`, `kill` and Gauss's lemma), so
  `∑_{d ∣ m} μ^± = ∑_{d ∣ m, p ∤ d} μ^± + ∑_{a ∣ m, p ∤ a} μ^∓`;
* `mobius_cancel` (`lem:mobius-cancel`, `m ≥ 2`): the two right sides agree, so
  `∑_{d ∣ m} μ⁺(d) = ∑_{d ∣ m} μ⁻(d)`, i.e. `∑_{d ∣ m} μ(d) = 0`;
* `mobius_one`: `∑_{d ∣ 1} μ⁺(d) = 1`, `∑_{d ∣ 1} μ⁻(d) = 0`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Mobius

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 isP_of_prime prime_of_isP eq_of_eqb_ne)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_unique val_mul not_dvd_one p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.Expectation (mul_one')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (pos_mul')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Definitions -/

/-- `[q prime] sg(v_q(x))`, over `0 = q`, `1 = x`. -/
abbrev omB : PTm 2 := isP (var 0) * sg (val (var 0) (var 1))
/-- `[q prime] sg(v_q(x) ∸ 1)`. -/
abbrev sqB : PTm 2 := isP (var 0) * sg (monus (val (var 0) (var 1)) one)

/-- `ω_N(x)`. -/
abbrev om (N x : PTm n) : PTm n := ap2 (sumF omB) N x
/-- `s_N(x)`. -/
abbrev sq (N x : PTm n) : PTm n := ap2 (sumF sqB) N x
/-- `μ⁺_N(x) = [s_N(x) = 0][ω_N(x) even]`. -/
abbrev muP (N x : PTm n) : PTm n := eqb (sq N x) zero * eqb (rem (om N x) two) zero
/-- `μ⁻_N(x) = [s_N(x) = 0][ω_N(x) odd]`. -/
abbrev muN (N x : PTm n) : PTm n := eqb (sq N x) zero * eqb (rem (om N x) two) one

theorem inst2_om (q x : PTm n) : inst2 omB q x = isP q * sg (val q x) := by simp [inst2]
theorem inst2_sq (q x : PTm n) : inst2 sqB q x = isP q * sg (monus (val q x) one) := by simp [inst2]

/-! ## Valuations at a prime -/

theorem prime_two {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] le two p := by
  unfold prime at hp; exact Prf.andE₁ hp

theorem congrVal {p p' m m' : PTm n} (h₁ : Γ ⊢[PRAAx] p ≐ p') (h₂ : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] val p m ≐ val p' m' :=
  congrAp2 (Search.muF _) (congrSucc h₂) (congrPairT h₁ h₂)

/-- A prime `q ≠ p` does not divide the prime `p`. -/
theorem not_dvd_prime {q p : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hp : Γ ⊢[PRAAx] prime p)
    (hne : Γ ⊢[PRAAx] neg (q ≐ p)) : Γ ⊢[PRAAx] neg (dvd q p) := by
  refine .impI ?_
  let C : List (Fm PTm n) := dvd q p :: Γ
  have hd : C ⊢[PRAAx] dvd q p := Prf.hyp0
  have hq1 := p_pos (prime_two hq.wk : C ⊢[PRAAx] _)
  have hp1 := p_pos (prime_two hp.wk : C ⊢[PRAAx] _)
  have hle := dvd_le' hq1 hd hp1
  refine .orE (lt_or_le q p) ?_ ?_
  · have hp' := (hp.wk (ψ := dvd q p)).wk (ψ := lt q p)
    unfold prime at hp'
    have a := Prf.allE q (Prf.andE₂ hp')
    simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at a
    exact Prf.impE (Prf.impE (Prf.impE a (prime_two hq.wk.wk)) Prf.hyp0) hd.wk
  · exact Prf.impE hne.wk.wk (le_antisymm hle.wk Prf.hyp0)

/-- `v_q(p) = [q = p]` for primes `q`, `p`. -/
theorem val_pp {q p : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] val q p ≐ eqb q p := by
  have hq2 := prime_two hq
  have hp1 := p_pos (prime_two hp)
  refine .orE (eq_or_ne q p) ?_ ?_
  · let C : List (Fm PTm n) := (q ≐ p) :: Γ
    have e : C ⊢[PRAAx] q ≐ p := Prf.hyp0
    have v : C ⊢[PRAAx] val q p ≐ one :=
      val_unique hq2.wk hp1.wk (c := one) (e.eqSymm.eqTrans ((pw_one q).eqSymm.eqTrans (by ipra_ring)))
        (not_dvd_one hq2.wk)
    exact v.eqTrans (eqb_of_eq e).eqSymm
  · let C : List (Fm PTm n) := neg (q ≐ p) :: Γ
    have v : C ⊢[PRAAx] val q p ≐ zero :=
      val_unique hq2.wk hp1.wk (c := p) ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero q).eqSymm (.eqRefl p)))
        (not_dvd_prime hq.wk hp.wk Prf.hyp0)
    exact v.eqTrans (eqb_of_ne Prf.hyp0).eqSymm

/-- `v_q(a p) = v_q(a) + [q = p]` for primes `q`, `p` and `a ≥ 1`. -/
theorem val_mul_prime {q a p : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hp : Γ ⊢[PRAAx] prime p)
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] val q (a * p) ≐ val q a + eqb q p :=
  (val_mul hq ha (p_pos (prime_two hp))).eqTrans (congrAdd (.eqRefl _) (val_pp hq hp))

/-! ## Pointwise effect of a prime factor -/

alias congrSg := Common.congrSg

alias congrEqb' := Common.congrEqb

theorem congrIsP {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] isP a ≐ isP b := by
  have e := Prf.eqCongr (Γ := Γ) (isP (var 0) : PTm 1) (σ := ![a]) (σ' := ![b]) (fun j => by fin_cases j; assumption)
  simpa using e

theorem isP_ne {q p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h0 : Γ ⊢[PRAAx] isP q ≐ zero) :
    Γ ⊢[PRAAx] neg (q ≐ p) := by
  refine .impI ?_
  have e : ((q ≐ p) :: Γ) ⊢[PRAAx] one ≐ zero :=
    (isP_of_prime hp.wk).eqSymm.eqTrans ((congrIsP Prf.hyp0).eqSymm.eqTrans h0.wk)
  exact succ_ne_zero' _ e

theorem zero_mul_l {x : PTm n} (h : Γ ⊢[PRAAx] x ≐ zero) (z : PTm n) : Γ ⊢[PRAAx] x * z ≐ zero :=
  (congrMul h (.eqRefl _)).eqTrans (by ipra_ring)

/-- `[q prime] sg(v_q(a p)) = [q prime] sg(v_q(a)) + [q = p]` for `p ∤ a`. -/
theorem om_pt {q a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hpa : Γ ⊢[PRAAx] val p a ≐ zero) : Γ ⊢[PRAAx] inst2 omB q (a * p) ≐ inst2 omB q a + eqb q p := by
  rw [inst2_om, inst2_om]
  refine .orE (isP_01 q) ?_ ?_
  · let C : List (Fm PTm n) := (isP q ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    have ne := eqb_of_ne (isP_ne hp.wk h0)
    exact (zero_mul_l h0 _).eqTrans ((congrAdd (zero_mul_l h0 _) ne).eqTrans (add_zero _)).eqSymm
  · let C : List (Fm PTm n) := (isP q ≐ one) :: Γ
    have h1 : C ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    have hv := val_mul_prime (prime_of_isP h1) hp.wk ha.wk
    refine .orE (eq_or_ne q p) ?_ ?_
    · let D : List (Fm PTm n) := (q ≐ p) :: C
      have e : D ⊢[PRAAx] q ≐ p := Prf.hyp0
      have v0 : D ⊢[PRAAx] val q a ≐ zero := (congrVal e (.eqRefl a)).eqTrans hpa.wk.wk
      have eb := eqb_of_eq e
      have s1 : D ⊢[PRAAx] sg (val q (a * p)) ≐ one :=
        (congrSg (hv.wk.eqTrans ((congrAdd v0 eb).eqTrans (zero_add _)))).eqTrans (sg_succ zero)
      have s0 : D ⊢[PRAAx] sg (val q a) ≐ zero := (congrSg v0).eqTrans sg_zero
      refine (congrMul h1.wk s1).eqTrans (.eqTrans ?_ (congrAdd (congrMul h1.wk s0) eb).eqSymm)
      ipra_ring
    · let D : List (Fm PTm n) := neg (q ≐ p) :: C
      have eb := eqb_of_ne (Prf.hyp0 : D ⊢[PRAAx] _)
      have s : D ⊢[PRAAx] sg (val q (a * p)) ≐ sg (val q a) :=
        congrSg (hv.wk.eqTrans ((congrAdd (.eqRefl _) eb).eqTrans (add_zero _)))
      exact (congrMul (.eqRefl _) s).eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) eb.eqSymm))

/-- `[q prime] sg(v_q(a p) ∸ 1) = [q prime] sg(v_q(a) ∸ 1)` for `p ∤ a`. -/
theorem sq_pt {q a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hpa : Γ ⊢[PRAAx] val p a ≐ zero) : Γ ⊢[PRAAx] inst2 sqB q (a * p) ≐ inst2 sqB q a := by
  rw [inst2_sq, inst2_sq]
  refine .orE (isP_01 q) ?_ ?_
  · have h0 : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    exact (zero_mul_l h0 _).eqTrans (zero_mul_l h0 _).eqSymm
  · let C : List (Fm PTm n) := (isP q ≐ one) :: Γ
    have h1 : C ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    have hv := val_mul_prime (prime_of_isP h1) hp.wk ha.wk
    refine congrMul (.eqRefl _) (congrSg ?_)
    refine .orE (eq_or_ne q p) ?_ ?_
    · let D : List (Fm PTm n) := (q ≐ p) :: C
      have e : D ⊢[PRAAx] q ≐ p := Prf.hyp0
      have v0 : D ⊢[PRAAx] val q a ≐ zero := (congrVal e (.eqRefl a)).eqTrans hpa.wk.wk
      have l : D ⊢[PRAAx] monus (val q (a * p)) one ≐ zero :=
        (congrMonus (hv.wk.eqTrans (congrAdd v0 (eqb_of_eq e))) (.eqRefl _)).eqTrans (add_monus _ _)
      exact l.eqTrans ((congrMonus v0 (.eqRefl _)).eqTrans (zero_monus _)).eqSymm
    · have eb := eqb_of_ne (Prf.hyp0 : (neg (q ≐ p) :: C) ⊢[PRAAx] _)
      exact congrMonus (hv.wk.eqTrans ((congrAdd (.eqRefl _) eb).eqTrans (add_zero _))) (.eqRefl _)

/-- `p² ∣ a p` when `p ∣ a`: the square indicator at `p` is `1`. -/
theorem sq_kill_pt {a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hpa : Γ ⊢[PRAAx] le one (val p a)) : Γ ⊢[PRAAx] inst2 sqB p (a * p) ≐ one := by
  rw [inst2_sq]
  have hv := val_mul_prime hp hp ha
  have m : Γ ⊢[PRAAx] monus (val p (a * p)) one ≐ val p a :=
    (congrMonus (hv.eqTrans (congrAdd (.eqRefl _) (eqb_of_eq (.eqRefl p)))) (.eqRefl _)).eqTrans (add_monus _ _)
  have w := eq_add_of_le hpa
  have s : Γ ⊢[PRAAx] sg (val p a) ≐ one :=
    (congrSg (w.eqTrans (by ipra_ring : Γ ⊢[PRAAx] one + monus (val p a) one ≐
      succ (monus (val p a) one)))).eqTrans (sg_succ _)
  refine (congrMul (isP_of_prime hp) ((congrSg m).eqTrans s)).eqTrans ?_
  ipra_ring

/-! ## Sums -/

/-- A body read at the second component of a pair parameter. -/
def lB (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_lB (f : PTm 2) (i z : PTm n) : inst2 (lB f) i z = inst2 f i (sndT z) := by
  simp only [inst2, lB, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem shift_mul' (a b : PTm n) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by simp [Syn.shift]

theorem one_inst (i z : PTm n) : inst2 (one : PTm 2) i z = one := by simp [inst2]

/-- `ω_N(a p) = ω_N(a) + 1` for a prime `p < N` with `p ∤ a`. -/
theorem om_mul {N a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpN : Γ ⊢[PRAAx] lt p N)
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hpa : Γ ⊢[PRAAx] val p a ≐ zero) :
    Γ ⊢[PRAAx] om N (a * p) ≐ succ (om N a) := by
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have ha' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift a ≐ succ (pred (Syn.shift a)) := by
    simpa [Fm.shift, Syn.shift] using ha.shift
  have hpa' : (Γ.map Fm.shift) ⊢[PRAAx] val (Syn.shift p) (Syn.shift a) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hpa.shift
  have c₁ : Γ ⊢[PRAAx] om N (a * p) ≐ ap2 (sumF (addBody (lB omB) (dB (one : PTm 2)))) N (pairT p a) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_lB, inst2_dB, one_inst, shift_pairT, shift_mul']
    refine (om_pt hp'.wk ha'.wk hpa'.wk).eqTrans (congrAdd (congrInst2 omB (.eqRefl _) (snd_pair _ _)).eqSymm ?_)
    exact (eqb_comm' _ _).eqTrans ((congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)).eqTrans (mul_one' _).eqSymm)
  have c₃ : Γ ⊢[PRAAx] ap2 (sumF (lB omB)) N (pairT p a) ≐ om N a := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_lB, shift_pairT]
    exact congrInst2 omB (.eqRefl _) (snd_pair _ _)
  have c₄ : Γ ⊢[PRAAx] ap2 (sumF (dB (one : PTm 2))) N (pairT p a) ≐ one :=
    (sum_delta (one : PTm 2) hpN).eqTrans (by rw [one_inst]; exact .eqRefl _)
  ipra_lc natEq c₁ + natEq (sum_add (lB omB) (dB (one : PTm 2)) N (pairT p a)) + natEq c₃ + natEq c₄

/-- `s_N(a p) = s_N(a)` for a prime `p` with `p ∤ a`. -/
theorem sq_mul {N a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hpa : Γ ⊢[PRAAx] val p a ≐ zero) : Γ ⊢[PRAAx] sq N (a * p) ≐ sq N a := by
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have ha' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift a ≐ succ (pred (Syn.shift a)) := by
    simpa [Fm.shift, Syn.shift] using ha.shift
  have hpa' : (Γ.map Fm.shift) ⊢[PRAAx] val (Syn.shift p) (Syn.shift a) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hpa.shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_mul']
  exact sq_pt hp'.wk ha'.wk hpa'.wk

/-- `s_N(a p) ≥ 1` for a prime `p < N` with `p ∣ a`. -/
theorem sq_kill {N a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpN : Γ ⊢[PRAAx] lt p N)
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hpa : Γ ⊢[PRAAx] le one (val p a)) :
    Γ ⊢[PRAAx] le one (sq N (a * p)) :=
  le_congr (sq_kill_pt hp ha hpa) (.eqRefl _) (term_le_sum sqB (x := a * p) hpN)

/-! ## Parity -/

theorem one_ne_zero' : Γ ⊢[PRAAx] neg ((one : PTm n) ≐ zero) := .impI (succ_ne_zero' _ Prf.hyp0)
theorem zero_ne_one' : Γ ⊢[PRAAx] neg ((zero : PTm n) ≐ one) := .impI (succ_ne_zero' _ (Prf.hyp0).eqSymm)

/-- Parity of `w + 1` against parity of `w`. -/
theorem par_succ (w : PTm n) :
    Γ ⊢[PRAAx] (eqb (rem (succ w) two) zero ≐ eqb (rem w two) one) ⋏
      (eqb (rem (succ w) two) one ≐ eqb (rem w two) zero) := by
  have rl := rem_lt' (two_pos' (Γ := Γ)) w
  refine .orE (zero_or_succ (rem w two)) ?_ ?_
  · let C : List (Fm PTm n) := (rem w two ≐ zero) :: Γ
    have r0 : C ⊢[PRAAx] rem w two ≐ zero := Prf.hyp0
    have e0 := natEq r0
    have dv := natEq (div_eq (Γ := C) (j := w) two_pos')
    have r1 : C ⊢[PRAAx] rem (succ w) two ≐ one :=
      rem_eq' two_pos' (q := quo w two) (by apply deriveNat; ipra_simps; linear_combination dv + e0)
        (le_refl _)
    refine .andI ((congrEqb' r1 (.eqRefl _)).eqTrans ((eqb_of_ne one_ne_zero').eqTrans
      ((congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one')).eqSymm)) ?_
    exact (congrEqb' r1 (.eqRefl _)).eqTrans ((eqb_of_eq (.eqRefl _)).eqTrans
      ((congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))).eqSymm)
  · let C : List (Fm PTm n) := (rem w two ≐ succ (pred (rem w two))) :: Γ
    have hs : C ⊢[PRAAx] rem w two ≐ succ (pred (rem w two)) := Prf.hyp0
    have r1 : C ⊢[PRAAx] rem w two ≐ one := by
      have l : C ⊢[PRAAx] le (pred (rem w two)) zero :=
        (succ_monus_succ _ _).eqSymm.eqTrans ((congrMonus hs.eqSymm (.eqRefl _)).eqTrans
          ((succ_monus_succ _ _).eqSymm.eqTrans rl.wk))
      exact hs.eqTrans (congrSucc (le_antisymm l (zero_le _)))
    have e1 := natEq r1
    have dv := natEq (div_eq (Γ := C) (j := w) two_pos')
    have r0 : C ⊢[PRAAx] rem (succ w) two ≐ zero :=
      rem_eq' two_pos' (q := succ (quo w two)) (by apply deriveNat; ipra_simps; linear_combination dv + e1)
        (zero_lt' two_pos')
    refine .andI ((congrEqb' r0 (.eqRefl _)).eqTrans ((eqb_of_eq (.eqRefl _)).eqTrans
      ((congrEqb' r1 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))).eqSymm)) ?_
    exact (congrEqb' r0 (.eqRefl _)).eqTrans ((eqb_of_ne zero_ne_one').eqTrans
      ((congrEqb' r1 (.eqRefl _)).eqTrans (eqb_of_ne one_ne_zero')).eqSymm)

/-! ## Swap and kill -/

/-- For `p ∤ a`: `μ⁺(a p) = μ⁻(a)` and `μ⁻(a p) = μ⁺(a)`. -/
theorem swap {N a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpN : Γ ⊢[PRAAx] lt p N)
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hpa : Γ ⊢[PRAAx] val p a ≐ zero) :
    Γ ⊢[PRAAx] (muP N (a * p) ≐ muN N a) ⋏ (muN N (a * p) ≐ muP N a) := by
  have s := congrEqb' (sq_mul (N := N) hp ha hpa) (.eqRefl zero)
  have o := congrAp2 remF (om_mul hp hpN ha hpa) (.eqRefl two)
  have pr := par_succ (Γ := Γ) (om N a)
  exact .andI (congrMul s ((congrEqb' o (.eqRefl _)).eqTrans (Prf.andE₁ pr)))
    (congrMul s ((congrEqb' o (.eqRefl _)).eqTrans (Prf.andE₂ pr)))

/-- For `p ∣ a`: `μ⁺(a p) = μ⁻(a p) = 0`. -/
theorem kill {N a p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hpN : Γ ⊢[PRAAx] lt p N)
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hpa : Γ ⊢[PRAAx] le one (val p a)) :
    Γ ⊢[PRAAx] (muP N (a * p) ≐ zero) ⋏ (muN N (a * p) ≐ zero) := by
  have l := sq_kill (N := N) hp hpN ha hpa
  have ne : Γ ⊢[PRAAx] neg (sq N (a * p) ≐ zero) :=
    .impI (not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 l.wk))
  have z := eqb_of_ne ne
  exact .andI (zero_mul_l z _) (zero_mul_l z _)

/-! ## Divisor sums -/

/-- `[d ≥ 1][d ∣ m]`, over `0 = d`, `1 = m`. -/
abbrev dvB : PTm 2 := sg (var 0) * eqb (rem (var 1) (var 0)) zero
/-- `[p ∣ d]` for `p = ℓ(m)`. -/
abbrev pdB : PTm 2 := eqb (rem (var 0) (lpf (var 1))) zero
/-- `[p ∤ d]`. -/
abbrev cpB : PTm 2 := monus one pdB
/-- `[d ∣ m] μ⁺(d)`. -/
abbrev PB : PTm 2 := dvB * muP (succ (var 1)) (var 0)
/-- `[d ∣ m] μ⁻(d)`. -/
abbrev NB : PTm 2 := dvB * muN (succ (var 1)) (var 0)

theorem inst2_PB (d M : PTm n) : inst2 PB d M = (sg d * eqb (rem M d) zero) * muP (succ M) d := by
  simp [inst2]
theorem inst2_NB (d M : PTm n) : inst2 NB d M = (sg d * eqb (rem M d) zero) * muN (succ M) d := by
  simp [inst2]
theorem inst2_cp (d M : PTm n) : inst2 cpB d M = monus one (eqb (rem d (lpf M)) zero) := by simp [inst2]
theorem inst2_pd (d M : PTm n) : inst2 pdB d M = eqb (rem d (lpf M)) zero := by simp [inst2]
theorem inst2_mulB (f g : PTm 2) (d M : PTm n) : inst2 (f * g) d M = inst2 f d M * inst2 g d M := by
  simp [inst2]

/-- `g(a, m) = F(a ℓ(m), m)`. -/
def mB (F : PTm 2) : PTm 2 := Syn.subst ![var 0 * lpf (var 1), var 1] F

theorem inst2_mB (F : PTm 2) (a M : PTm n) : inst2 (mB F) a M = inst2 F (a * lpf M) M := by
  simp only [inst2, mB, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

alias pos_of_two := Common.pos_of_two_le

theorem eqb_split (a b : PTm n) : Γ ⊢[PRAAx] monus one (eqb a b) + eqb a b ≐ one := by
  unfold eqb
  refine .orE (zero_or_succ (monus a b + monus b a)) ?_ ?_
  · have h : ((monus a b + monus b a ≐ zero) :: Γ) ⊢[PRAAx] monus one (monus a b + monus b a) ≐ one :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    exact (congrAdd ((congrMonus (.eqRefl _) h).eqTrans (monus_self _)) h).eqTrans (zero_add _)
  · have h : ((monus a b + monus b a ≐ succ (pred (monus a b + monus b a))) :: Γ) ⊢[PRAAx]
        monus one (monus a b + monus b a) ≐ zero :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))
    exact (congrAdd ((congrMonus (.eqRefl _) h).eqTrans (monus_zero _)) h).eqTrans (add_zero _)

section Divisors

variable {M : PTm n}

/-- The multiples `a ℓ(m)` of the least prime factor: `[a p ∣ m] μ^±(a p) = [p ∤ a] [a ∣ m] μ^∓(a)`. -/
theorem mult_pt (hM : Γ ⊢[PRAAx] le two M) (a : PTm n) :
    Γ ⊢[PRAAx] (inst2 PB (a * lpf M) M ≐ inst2 cpB a M * inst2 NB a M) ⋏
      (inst2 NB (a * lpf M) M ≐ inst2 cpB a M * inst2 PB a M) := by
  rw [inst2_PB, inst2_NB, inst2_cp, inst2_PB, inst2_NB]
  have hp := lpf_prime' hM
  have hpd := lpf_dvd' hM
  have hp1 : Γ ⊢[PRAAx] lpf M ≐ succ (pred (lpf M)) := p_pos (prime_two hp)
  have hM1 := pos_of_two hM
  have hpN : Γ ⊢[PRAAx] lt (lpf M) (succ M) := (succ_monus_succ _ _).eqTrans (dvd_le' hp1 hpd hM1)
  refine .orE (zero_or_succ a) ?_ ?_
  · let C : List (Fm PTm n) := (a ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] a ≐ zero := Prf.hyp0
    have s0 : C ⊢[PRAAx] sg (a * lpf M) ≐ zero :=
      (congrSg ((congrMul h0 (.eqRefl _)).eqTrans (by ipra_ring))).eqTrans sg_zero
    have c0 : C ⊢[PRAAx] monus one (eqb (rem a (lpf M)) zero) ≐ zero :=
      (congrMonus (.eqRefl _) (eqb_of_eq ((congrAp2 remF h0 (.eqRefl _)).eqTrans (rem_zero _)))).eqTrans
        (monus_self _)
    exact .andI ((zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l c0 _).eqSymm)
      ((zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l c0 _).eqSymm)
  · let C : List (Fm PTm n) := (a ≐ succ (pred a)) :: Γ
    have ha : C ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
    refine .orE (eq_or_ne (rem a (lpf M)) zero) ?_ ?_
    · let D : List (Fm PTm n) := (rem a (lpf M) ≐ zero) :: C
      have hd : D ⊢[PRAAx] rem a (lpf M) ≐ zero := Prf.hyp0
      have hv1 : D ⊢[PRAAx] le one (val (lpf M) a) := by
        refine .orE (lt_or_le zero (val (lpf M) a)) Prf.hyp0 ?_
        have v0 : (le (val (lpf M) a) zero :: D) ⊢[PRAAx] val (lpf M) a ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
        have nd : (le (val (lpf M) a) zero :: D) ⊢[PRAAx] neg (dvd (pw (lpf M) (succ (val (lpf M) a))) a) :=
          Valuation.val_not_dvd (prime_two hp).wk.wk.wk ha.wk.wk
        have e : (le (val (lpf M) a) zero :: D) ⊢[PRAAx] pw (lpf M) (succ (val (lpf M) a)) ≐ lpf M :=
          (congrPw (.eqRefl _) (congrSucc v0)).eqTrans (pw_one _)
        exact .botE _ (Prf.impE nd ((congrAp2 remF (.eqRefl _) e).eqTrans hd.wk))
      have k := kill (N := succ M) hp.wk.wk hpN.wk.wk ha.wk hv1
      have c1 : D ⊢[PRAAx] monus one (eqb (rem a (lpf M)) zero) ≐ zero :=
        (congrMonus (.eqRefl _) (eqb_of_eq hd)).eqTrans (monus_self _)
      have zr : ∀ {x : PTm n}, D ⊢[PRAAx] x * zero ≐ zero := fun {x} => by ipra_ring
      exact .andI ((congrMul (.eqRefl _) (Prf.andE₁ k)).eqTrans (zr.eqTrans (zero_mul_l c1 _).eqSymm))
        ((congrMul (.eqRefl _) (Prf.andE₂ k)).eqTrans (zr.eqTrans (zero_mul_l c1 _).eqSymm))
    · let D : List (Fm PTm n) := neg (rem a (lpf M) ≐ zero) :: C
      have hna : D ⊢[PRAAx] neg (dvd (lpf M) a) := Prf.hyp0
      have c1 : D ⊢[PRAAx] monus one (eqb (rem a (lpf M)) zero) ≐ one :=
        (congrMonus (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (monus_zero _)
      have hv0 : D ⊢[PRAAx] val (lpf M) a ≐ zero :=
        val_unique (prime_two hp).wk.wk ha.wk (c := a)
          ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero _).eqSymm (.eqRefl a))) hna
      have sw := swap (N := succ M) hp.wk.wk hpN.wk.wk ha.wk hv0
      have hap : D ⊢[PRAAx] a * lpf M ≐ succ (pred (a * lpf M)) := pos_mul' ha.wk hp1.wk.wk
      have sgap : D ⊢[PRAAx] sg (a * lpf M) ≐ one := (congrSg hap).eqTrans (sg_succ _)
      have sga : D ⊢[PRAAx] sg a ≐ one := (congrSg ha.wk).eqTrans (sg_succ _)
      have eqbE : D ⊢[PRAAx] eqb (rem M (a * lpf M)) zero ≐ eqb (rem M a) zero := by
        refine .orE (eq_or_ne (rem M a) zero) ?_ ?_
        · let E : List (Fm PTm n) := (rem M a ≐ zero) :: D
          have hdM : E ⊢[PRAAx] dvd a M := Prf.hyp0
          have eM := eq_of_dvd' ha.wk.wk hdM
          have hpk : E ⊢[PRAAx] dvd (lpf M) (quo M a) :=
            gauss hp1.wk.wk.wk (gcd_prime hp.wk.wk.wk hna.wk)
              ((congrAp2 remF eM.eqSymm (.eqRefl _)).eqTrans hpd.wk.wk.wk)
          have eM' := natEq eM
          have eq2 : E ⊢[PRAAx] M ≐ a * lpf M * quo (quo M a) (lpf M) := by
            ipra_lc eM' + 𝔞 a * natEq (eq_of_dvd' hp1.wk.wk.wk hpk)
          have hd2 : E ⊢[PRAAx] dvd (a * lpf M) M := dvd_of_eq' hap.wk eq2
          exact (eqb_of_eq hd2).eqTrans (eqb_of_eq hdM).eqSymm
        · let E : List (Fm PTm n) := neg (rem M a ≐ zero) :: D
          have ne : E ⊢[PRAAx] neg (dvd (a * lpf M) M) := by
            refine .impI ?_
            have e := natEq (eq_of_dvd' hap.wk.wk (Prf.hyp0 : (dvd (a * lpf M) M :: E) ⊢[PRAAx] _))
            have eq3 : (dvd (a * lpf M) M :: E) ⊢[PRAAx] M ≐ a * (lpf M * quo M (a * lpf M)) := by
              ipra_lc e
            have hdM : (dvd (a * lpf M) M :: E) ⊢[PRAAx] dvd a M := dvd_of_eq' ha.wk.wk.wk eq3
            exact Prf.impE Prf.hyp1 hdM
          exact (eqb_of_ne ne).eqTrans (eqb_of_ne Prf.hyp0).eqSymm
      have dvE : D ⊢[PRAAx] sg (a * lpf M) * eqb (rem M (a * lpf M)) zero ≐ sg a * eqb (rem M a) zero :=
        congrMul (sgap.eqTrans sga.eqSymm) eqbE
      have one_l : ∀ {x : PTm n}, D ⊢[PRAAx] monus one (eqb (rem a (lpf M)) zero) * x ≐ x :=
        fun {x} => (congrMul c1 (.eqRefl x)).eqTrans (one_mul x)
      exact .andI ((congrMul dvE (Prf.andE₁ sw)).eqTrans one_l.eqSymm)
        ((congrMul dvE (Prf.andE₂ sw)).eqTrans one_l.eqSymm)

/-- Beyond `m`, no divisor: `[d ∣ m] μ^±(d) = 0` for `d > m ≥ 2`. -/
theorem tail_pt {d : PTm n} (hM : Γ ⊢[PRAAx] le two M) (h : Γ ⊢[PRAAx] lt M d) :
    Γ ⊢[PRAAx] (inst2 PB d M ≐ zero) ⋏ (inst2 NB d M ≐ zero) := by
  rw [inst2_PB, inst2_NB]
  have w := natEq (eq_add_of_le h)
  have hd : Γ ⊢[PRAAx] d ≐ succ (pred d) :=
    eq_succ_pred (y := M + monus d (succ M)) (by ipra_lc w)
  have r : Γ ⊢[PRAAx] rem M d ≐ M := rem_eq' hd (q := zero) (by ipra_ring) h
  have hM1 := pos_of_two hM
  have z : Γ ⊢[PRAAx] eqb (rem M d) zero ≐ zero :=
    (congrEqb' r (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (hM1.wk.eqSymm.eqTrans Prf.hyp0))))
  have zz : ∀ {x : PTm n}, Γ ⊢[PRAAx] (sg d * eqb (rem M d) zero) * x ≐ zero := fun {x} =>
    zero_mul_l ((congrMul (.eqRefl _) z).eqTrans (by ipra_ring)) x
  exact .andI zz zz

end Divisors

/-- Split by `[p ∣ d]` and reindex the multiples of `p = ℓ(m)`:
`∑_{d ≤ m} F(d) = ∑_{d ≤ m} [p ∤ d] F(d) + ∑_{a ≤ m} [p ∤ a] G(a)` whenever `F(a p) = [p ∤ a] G(a)`
and `F` vanishes beyond `m`. -/
theorem split_reindex (F G : PTm 2) {M : PTm n} (hM : Γ ⊢[PRAAx] le two M)
    (hH : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {M' : PTm k} (a : PTm k), (Δ ⊢[PRAAx] le two M') →
      (Δ ⊢[PRAAx] inst2 F (a * lpf M') M' ≐ inst2 cpB a M' * inst2 G a M'))
    (hT : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {M' d : PTm k}, (Δ ⊢[PRAAx] le two M') → (Δ ⊢[PRAAx] lt M' d) →
      (Δ ⊢[PRAAx] inst2 F d M' ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF F) (succ M) M ≐
      ap2 (sumF (cpB * F)) (succ M) M + ap2 (sumF (cpB * G)) (succ M) M := by
  have hM' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift M) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hp := lpf_prime' hM
  have hp1 : Γ ⊢[PRAAx] lpf M ≐ succ (pred (lpf M)) := p_pos (prime_two hp)
  -- split pointwise
  have sp : Γ ⊢[PRAAx] ap2 (sumF F) (succ M) M ≐ ap2 (sumF (addBody (cpB * F) (pdB * F))) (succ M) M := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_mulB, inst2_mulB, inst2_cp, inst2_pd]
    have e := natEq (eqb_split (Γ := lt (var 0) (Syn.shift (succ M)) :: Γ.map Fm.shift)
      (rem (var 0) (lpf (Syn.shift M))) zero)
    ipra_lc (-𝔞 (inst2 F (var 0) (Syn.shift M))) * e
  -- extend the multiple part to `(succ M + pred (lpf M) * M) = (M + 1) + (p − 1) M`
  have ex : Γ ⊢[PRAAx] ap2 (sumF (pdB * F)) (succ M + pred (lpf M) * M) M ≐ ap2 (sumF (pdB * F)) (succ M) M := by
    refine (sum_split (pdB * F) (succ M) (pred (lpf M) * M) M).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _))
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    have hs : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
    rw [inst2_offB, shift_pairT, inst2_mulB, hs]
    refine (congrMul (.eqRefl _) ((congrInst2 F (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
      (hT hM'.wk ?_))).eqTrans (by ipra_ring)
    exact le_of_eq_add (d := var 0) (by apply deriveNat; ipra_simps; try ring)
  -- reindex
  have r₁ : Γ ⊢[PRAAx] ap2 (sumF (pdB * F)) (succ M + pred (lpf M) * M) M ≐
      ap3 (sum2F (GcdFiber.rB (mB F))) (succ M + pred (lpf M) * M) (lpf M) M := by
    refine (SumPhi.sum2_eq_sum (pdB * F) (succ M + pred (lpf M) * M) (lpf M) M).eqSymm.eqTrans ?_
    refine sum2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [GcdFiber.inst3_rB, inst2_mB]
    have e₀ : inst3 (Syn.subst ![var 0, var 2] (pdB * F)) (var 0 : PTm (n + 1)) (Syn.shift (lpf M)) (Syn.shift M) =
        inst2 (pdB * F) (var 0) (Syn.shift M) := by
      simp only [inst3, inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
    rw [e₀, inst2_mulB, inst2_pd]
    have sl : Syn.shift (lpf M) = lpf (Syn.shift M) := by simp [Syn.shift]
    rw [sl]
    refine .orE (eq_or_ne (rem (var 0) (lpf (Syn.shift M))) zero) ?_ ?_
    · let C₀ : List (Fm PTm (n + 1)) := (rem (var 0) (lpf (Syn.shift M)) ≐ zero) ::
        lt (var 0) (Syn.shift (succ M + pred (lpf M) * M)) :: Γ.map Fm.shift
      have hp1' : C₀ ⊢[PRAAx] lpf (Syn.shift M) ≐ succ (pred (lpf (Syn.shift M))) :=
        p_pos (prime_two (lpf_prime' hM'.wk.wk))
      have eq := eq_of_dvd' hp1' (Prf.hyp0 : C₀ ⊢[PRAAx] _)
      exact congrMul (.eqRefl _) (congrInst2 F (eq.eqTrans (mul_comm _ _)) (.eqRefl _))
    · have z := eqb_of_ne (Prf.hyp0 : (neg (rem (var 0) (lpf (Syn.shift M)) ≐ zero) ::
        lt (var 0) (Syn.shift (succ M + pred (lpf M) * M)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
      exact (zero_mul_l z _).eqTrans (zero_mul_l z _).eqSymm
  have r₂ := GcdFiber.reindex (mB F) (K := (succ M + pred (lpf M) * M)) (x := M) hp1
  have bq : Γ ⊢[PRAAx] quo ((succ M + pred (lpf M) * M) + pred (lpf M)) (lpf M) ≐ succ M :=
    quo_eq hp1 (r := zero) (by
      ipra_lc -(𝔞 M + 1) * natEq hp1) (zero_lt' hp1)
  have r₃ : Γ ⊢[PRAAx] ap2 (sumF (mB F)) (succ M) M ≐ ap2 (sumF (cpB * G)) (succ M) M := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_mB, inst2_mulB]
    exact hH _ hM'.wk
  ipra_lc natEq sp + natEq (sum_add (cpB * F) (pdB * F) (succ M) M) - natEq ex + natEq r₁ + natEq r₂ +
    natEq (congrAp2 (sumF (mB F)) bq (.eqRefl M)) + natEq r₃

/-- `lem:mobius-cancel` for `m ≥ 2`: `∑_{d ∣ m} μ⁺(d) = ∑_{d ∣ m} μ⁻(d)`, i.e. `∑_{d ∣ m} μ(d) = 0`. -/
theorem mobius_cancel {M : PTm n} (hM : Γ ⊢[PRAAx] le two M) :
    Γ ⊢[PRAAx] ap2 (sumF PB) (succ M) M ≐ ap2 (sumF NB) (succ M) M := by
  ipra_lc natEq (split_reindex PB NB hM (fun a h => Prf.andE₁ (mult_pt h a)) (fun h₁ h₂ => Prf.andE₁ (tail_pt h₁ h₂))) -
    natEq (split_reindex NB PB hM (fun a h => Prf.andE₂ (mult_pt h a)) (fun h₁ h₂ => Prf.andE₂ (tail_pt h₁ h₂)))

/-! ## The case `m = 1` -/

theorem isP_zero : Γ ⊢[PRAAx] isP (zero : PTm n) ≐ zero :=
  zero_mul_l ((congrSg (zero_monus _)).eqTrans sg_zero) _

theorem isP_one : Γ ⊢[PRAAx] isP (one : PTm n) ≐ zero :=
  zero_mul_l ((congrSg (monus_self _)).eqTrans sg_zero) _

theorem om_two_one : Γ ⊢[PRAAx] om (succ one) (one : PTm n) ≐ zero := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd ((sum_succ' _ _ _).eqTrans
    ((congrAdd (sum_zero _ _) ?_).eqTrans (zero_add _))) ?_).eqTrans (add_zero _))
  · rw [inst2_om]; exact zero_mul_l isP_zero _
  · rw [inst2_om]; exact zero_mul_l isP_one _

theorem sq_two_one : Γ ⊢[PRAAx] sq (succ one) (one : PTm n) ≐ zero := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd ((sum_succ' _ _ _).eqTrans
    ((congrAdd (sum_zero _ _) ?_).eqTrans (zero_add _))) ?_).eqTrans (add_zero _))
  · rw [inst2_sq]; exact zero_mul_l isP_zero _
  · rw [inst2_sq]; exact zero_mul_l isP_one _

/-- `lem:mobius-cancel` for `m = 1`: `∑_{d ∣ 1} μ⁺(d) = 1` and `∑_{d ∣ 1} μ⁻(d) = 0`, i.e. `μ(1) = 1`. -/
theorem mobius_one :
    Γ ⊢[PRAAx] (ap2 (sumF PB) (succ one) (one : PTm n) ≐ one) ⋏ (ap2 (sumF NB) (succ one) (one : PTm n) ≐ zero) := by
  have hone : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have r : Γ ⊢[PRAAx] rem (one : PTm n) one ≐ zero :=
    rem_eq' hone (q := one) (by ipra_ring) (zero_lt' hone)
  have dv1 : Γ ⊢[PRAAx] sg (one : PTm n) * eqb (rem one one) zero ≐ one :=
    (congrMul (sg_succ _) ((congrEqb' r (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)))).eqTrans
      (by ipra_ring)
  have s0 : Γ ⊢[PRAAx] eqb (sq (succ one) (one : PTm n)) zero ≐ one :=
    (congrEqb' sq_two_one (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))
  have o0 : Γ ⊢[PRAAx] rem (om (succ one) (one : PTm n)) two ≐ zero :=
    (congrAp2 remF om_two_one (.eqRefl _)).eqTrans (rem_zero _)
  have mp : Γ ⊢[PRAAx] muP (succ one) (one : PTm n) ≐ one :=
    (congrMul s0 ((congrEqb' o0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)))).eqTrans
      (by ipra_ring)
  have mn : Γ ⊢[PRAAx] muN (succ one) (one : PTm n) ≐ zero :=
    (congrMul s0 ((congrEqb' o0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one'))).eqTrans
      (by ipra_ring)
  have p0 : ∀ {X : PTm n}, Γ ⊢[PRAAx] (sg (zero : PTm n) * eqb (rem one zero) zero) * X ≐ zero :=
    fun {X} => zero_mul_l (zero_mul_l sg_zero _) X
  have two_sum : ∀ (B : PTm 2), Γ ⊢[PRAAx] ap2 (sumF B) (succ one) (one : PTm n) ≐
      inst2 B zero one + inst2 B one one := fun B =>
    (sum_succ' _ _ _).eqTrans (congrAdd ((sum_succ' _ _ _).eqTrans
      ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _))) (.eqRefl _))
  refine .andI ((two_sum PB).eqTrans ?_) ((two_sum NB).eqTrans ?_)
  · rw [inst2_PB, inst2_PB]
    exact (congrAdd p0 ((congrMul dv1 mp).eqTrans (by ipra_ring))).eqTrans (zero_add _)
  · rw [inst2_NB, inst2_NB]
    exact (congrAdd p0 ((congrMul dv1 mn).eqTrans (by ipra_ring))).eqTrans (add_zero _)

end LeanProofs.IPRA.AnalyticNumberTheory.Mobius

export_ipra AnalyticNumberTheory.Mobius (congrIsP congrSg congrVal inst2_mulB isP_zero muN one_inst zero_mul_l)
