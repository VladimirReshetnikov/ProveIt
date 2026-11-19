import IPRADerivations.Combinatorics.BellPeriodNp
import IPRADerivations.Foundations.BoundedReflection

/-!
# The least period of the Bell numbers modulo a prime divides `N_p` (`bell_numbers_ipra`, `thm:prime-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:prime-period`, last sentence: "The least positive period exists by bounded search and
divides `N_p`." Proof: "A candidate period `t` can be tested by the `p` congruences
`B_{t+i} ≡ B_i` for `0 ≤ i < p`. The order-`p` recurrence (touchard) propagates those
congruences to every subsequent index. Search `1 ≤ t ≤ N_p` for the least passing value `T`;
the preceding paragraph supplies a passing value. Divide `N_p = qT + s`, `0 ≤ s < T`. Repeated
use of period `T` and period `N_p` gives `B_{n+s} ≡ B_n` for every `n`. If `s > 0`, it passes
the same finite test, contrary to minimality. Therefore `s = 0`."

* `Test t p`: the bit of the `p` congruences `B_{t+i} ≡ B_i (mod p)`, `i < p`;
* `propagate_all`, `period_of_test`: a passing `t` is a period at every index. The
  propagation is a course-of-values induction (index `n ≥ p` uses the indices `n − p` and
  `n − p + 1`); the statement about all earlier indices is one bit;
* `period_mul`: then every multiple `q t` is a period;
* `np_test`: `N_p` passes the test (`Combinatorics/BellPeriodNp`);
* `T0 p`: the least passing positive value, by the bounded-search witness;
  `t0_test`, `least_period` (`B_{T + n} ≡ B_n` for all `n`), `least_minimal` (no smaller
  positive value passes the test);
* `s_test`, `least_dvd`: the remainder of `N_p` by `T` passes the test, hence is zero:
  `T ∣ N_p`.

Not derived: `thm:all-moduli-period`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellLeastPeriod

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchard (touchard)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (cong_add cong_of_eq shift_pair)
open LeanProofs.IPRA.Combinatorics.BellPeriodNp (Np Np_split bell_period_Np)
open LeanProofs.IPRA.Combinatorics.LinearFactorTable (pair_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB allB_zero allB_succ all_elim all_intro
  all_cases exB wit ex_intro ex_elim ex_least)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.Signum (sg sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The finite test -/

/-- The bit `[B_{t+i} ≡ B_i (mod p)]`, over `0 = i`, `1 = ⟨t, p⟩`. -/
abbrev eB : PTm 2 :=
  eqb (rem (bell (fstT (var 1) + var 0)) (sndT (var 1))) (rem (bell (var 0)) (sndT (var 1)))

theorem e_at (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 eB i (pairT t p) ≐ eqb (rem (bell (t + i)) p) (rem (bell i) p) := by
  have h : inst2 eB i (pairT t p) = eqb (rem (bell (fstT (pairT t p) + i)) (sndT (pairT t p)))
      (rem (bell i) (sndT (pairT t p))) := by simp [inst2]
  rw [h]
  exact congrEqb (congrAp2 remF (congrBell (congrAdd (fst_pair _ _) (.eqRefl _))) (snd_pair _ _))
    (congrAp2 remF (.eqRefl _) (snd_pair _ _))

theorem e_elim {i t p : PTm n} (h : Γ ⊢[PRAAx] neg (inst2 eB i (pairT t p) ≐ zero)) :
    Γ ⊢[PRAAx] rem (bell (t + i)) p ≐ rem (bell i) p :=
  eq_of_eqb_ne (.impI (.impE h.wk ((e_at i t p).eqTrans Prf.hyp0)))

theorem e_intro {i t p : PTm n} (h : Γ ⊢[PRAAx] rem (bell (t + i)) p ≐ rem (bell i) p) :
    Γ ⊢[PRAAx] inst2 eB i (pairT t p) ≐ one :=
  (e_at i t p).eqTrans (eqb_of_eq h)

theorem ne_of_one {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ one) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (Foundations.BoundedReflection.one_ne_zero _ (h.wk.eqSymm.eqTrans Prf.hyp0))

/-- The `p` congruences `B_{t+i} ≡ B_i`, `i < p`, as one bit. -/
abbrev Test (t p : PTm n) : PTm n := allB eB p (pairT t p)

theorem congrTest {t t' p : PTm n} (h : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx] Test t p ≐ Test t' p :=
  congrAp2 _ (.eqRefl _) (pair_congr h (.eqRefl _))

/-- One more index in a bounded universal bit. -/
theorem allB_extend (f : PTm 2) {N x : PTm n} (hQ : Γ ⊢[PRAAx] allB f N x ≐ one)
    (hf : Γ ⊢[PRAAx] inst2 f N x ≐ one) : Γ ⊢[PRAAx] allB f (succ N) x ≐ one :=
  (allB_succ f N x).eqTrans ((congrMul hQ
    ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hf)).eqTrans (sg_succ zero))).eqTrans
      (one_mul one))

/-! ## Propagation by the order-`p` recurrence -/

/-- An index `N ≥ p`: from the indices `N − p` and `N − p + 1`. -/
theorem big_case {t p N : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hQ : Γ ⊢[PRAAx] allB eB N (pairT t p) ≐ one) (hle : Γ ⊢[PRAAx] le p N) :
    Γ ⊢[PRAAx] rem (bell (t + N)) p ≐ rem (bell N) p := by
  have hq := prime_eq_succ_pred hp
  have h2 := prime_eq_succ_succ hp
  have eN := eq_add_of_le hle
  have lt1 : Γ ⊢[PRAAx] lt (monus N p) N := by
    refine le_of_eq_add (d := pred p) ?_
    have a := natEq eN
    have b := natEq hq
    apply deriveNat; ipra_simps
    linear_combination a + b
  have lt2 : Γ ⊢[PRAAx] lt (succ (monus N p)) N := by
    refine le_of_eq_add (d := monus p two) ?_
    have a := natEq eN
    have b := natEq h2
    apply deriveNat; ipra_simps
    linear_combination a + b
  have c0 := e_elim (all_elim eB hQ lt1)
  have c1 := e_elim (all_elim eB hQ lt2)
  have t1 := touchard hp (t + monus N p)
  have t0 := touchard hp (monus N p)
  have e₁ : Γ ⊢[PRAAx] t + N ≐ p + (t + monus N p) := by
    have a := natEq eN
    apply deriveNat; ipra_simps
    linear_combination a
  have e₂ : Γ ⊢[PRAAx] succ (t + monus N p) ≐ t + succ (monus N p) := by
    apply deriveNat; ipra_simps; ring
  refine (cong_of_eq (congrBell e₁)).eqTrans (t1.eqTrans ?_)
  refine (cong_add hq ((cong_of_eq (congrBell e₂)).eqTrans c1) c0).eqTrans ?_
  exact t0.eqSymm.eqTrans (cong_of_eq (congrBell eN.eqSymm))

theorem propagate_step {t p N : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hT : Γ ⊢[PRAAx] Test t p ≐ one) (hQ : Γ ⊢[PRAAx] allB eB N (pairT t p) ≐ one) :
    Γ ⊢[PRAAx] allB eB (succ N) (pairT t p) ≐ one :=
  allB_extend eB hQ (e_intro (.orE (lt_or_le N p)
    (e_elim (all_elim eB hT.wk Prf.hyp0)) (big_case hp.wk hQ.wk Prf.hyp0)))

/-- The induction formula; variable `0` is the number of indices reached. -/
abbrev propF (t p : PTm n) : Fm PTm (n + 1) :=
  allB eB (var 0) (pairT (Syn.shift t) (Syn.shift p)) ≐ one

/-- A passing candidate satisfies the congruence at every index below any bound. -/
theorem propagate_all {t p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hT : Γ ⊢[PRAAx] Test t p ≐ one)
    (N : PTm n) : Γ ⊢[PRAAx] allB eB N (pairT t p) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (propF t p) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using allB_zero (Γ := Γ) eB (pairT t p)
    · have hT' : (Γ.map Fm.shift) ⊢[PRAAx] Test (Syn.shift t) (Syn.shift p) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hT.shift
      have st : (propF t p :: Γ.map Fm.shift) ⊢[PRAAx]
          allB eB (succ (var 0)) (pairT (Syn.shift t) (Syn.shift p)) ≐ one :=
        propagate_step (prime_shift hp).wk hT'.wk Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE N hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- A passing candidate is a period: `B_{t+N} ≡ B_N (mod p)` for every `N`. -/
theorem period_of_test {t p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hT : Γ ⊢[PRAAx] Test t p ≐ one)
    (N : PTm n) : Γ ⊢[PRAAx] rem (bell (t + N)) p ≐ rem (bell N) p :=
  e_elim (all_elim eB (propagate_all hp hT (succ N)) (le_refl (succ N)))

/-- The induction formula of `period_mul`; variable `0` is the multiplier. -/
abbrev mulF (t p N : PTm n) : Fm PTm (n + 1) :=
  rem (bell (var 0 * Syn.shift t + Syn.shift N)) (Syn.shift p) ≐
    rem (bell (Syn.shift N)) (Syn.shift p)

/-- Every multiple of a period is a period. -/
theorem period_mul {t p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hT : Γ ⊢[PRAAx] Test t p ≐ one)
    (q N : PTm n) : Γ ⊢[PRAAx] rem (bell (q * t + N)) p ≐ rem (bell N) p := by
  have hall : Γ ⊢[PRAAx] Fm.all (mulF t p N) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] rem (bell (zero * t + N)) p ≐ rem (bell N) p :=
        cong_of_eq (congrBell (by apply deriveNat; ipra_simps; ring))
      simpa using b
    · have hT' : (Γ.map Fm.shift) ⊢[PRAAx] Test (Syn.shift t) (Syn.shift p) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hT.shift
      have st : (mulF t p N :: Γ.map Fm.shift) ⊢[PRAAx]
          rem (bell (succ (var 0) * Syn.shift t + Syn.shift N)) (Syn.shift p) ≐
            rem (bell (Syn.shift N)) (Syn.shift p) :=
        (cong_of_eq (congrBell (a := succ (var 0) * Syn.shift t + Syn.shift N)
          (b := Syn.shift t + (var 0 * Syn.shift t + Syn.shift N))
          (by apply deriveNat; ipra_simps; ring))).eqTrans
          ((period_of_test (prime_shift hp).wk hT'.wk _).eqTrans Prf.hyp0)
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE q hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-! ## `N_p` passes the test -/

theorem shift_Np (p : PTm n) : Syn.shift (Np p) = Np (Syn.shift p) := by simp [Syn.shift]

theorem np_test {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] Test (Np p) p ≐ one := by
  refine all_intro eB (.allI (.impI ?_))
  rw [shift_pair, shift_Np]
  exact ne_of_one (e_intro ((cong_of_eq (congrBell (add_comm _ _))).eqTrans
    (bell_period_Np (prime_shift hp).wk (var 0))))

theorem Np_pos {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] Np p ≐ succ (pred (Np p)) :=
  (Np_split hq).eqTrans
    (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred (Np_split hq).eqSymm)))

/-! ## The least passing value -/

/-- The bit `Test (s + 1) p`, over `0 = s`, `1 = p`. -/
abbrev pB : PTm 2 := allB eB (var 1) (pairT (succ (var 0)) (var 1))

theorem p_at (s p : PTm n) : inst2 pB s p = Test (succ s) p := by simp [inst2]

/-- The least `s < N_p` with `Test (s + 1) p`. -/
abbrev wT (p : PTm n) : PTm n := wit pB (Np p) p

/-- The least passing positive value. -/
abbrev T0 (p : PTm n) : PTm n := succ (wT p)

theorem ex_one {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] exB pB (Np p) p ≐ one := by
  have hq := prime_eq_succ_pred hp
  refine ex_intro pB (i := pred (Np p)) ?_ (le_congr (Np_pos hq) (.eqRefl _) (le_refl _))
  rw [p_at]
  exact ne_of_one ((congrTest (Np_pos hq)).eqSymm.eqTrans (np_test hp))

/-- The least value passes the test. -/
theorem t0_test {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] Test (T0 p) p ≐ one := by
  have ne := Prf.andE₂ (ex_elim pB (ex_one hp))
  rw [p_at] at ne
  exact .orE (all_cases eB p (pairT (T0 p) p)) (.botE _ (.impE ne.wk Prf.hyp0)) Prf.hyp0

/-- `thm:prime-period`: the least passing value is a period. -/
theorem least_period {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (T0 p + N)) p ≐ rem (bell N) p :=
  period_of_test hp (t0_test hp) N

/-- No smaller positive value passes the test. -/
theorem least_minimal {p s : PTm n} (h : Γ ⊢[PRAAx] lt s (wT p)) :
    Γ ⊢[PRAAx] Test (succ s) p ≐ zero := by
  have z := ex_least pB h
  rw [p_at] at z
  exact z

/-! ## The least period divides `N_p` -/

theorem s_point {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (i : PTm n) :
    Γ ⊢[PRAAx] rem (bell (rem (Np p) (T0 p) + i)) p ≐ rem (bell i) p := by
  have dm := Prf.andE₁ (div_mod (Γ := Γ) (Np p) (wT p))
  have pm := period_mul hp (t0_test hp) (quo (Np p) (T0 p)) (rem (Np p) (T0 p) + i)
  have e : Γ ⊢[PRAAx] quo (Np p) (T0 p) * T0 p + (rem (Np p) (T0 p) + i) ≐ i + Np p := by
    have a := natEq dm
    apply deriveNat; ipra_simps
    linear_combination -a
  exact pm.eqSymm.eqTrans ((cong_of_eq (congrBell e)).eqTrans (bell_period_Np hp i))

theorem shift_s (p : PTm n) : Syn.shift (pairT (rem (Np p) (T0 p)) p) =
    pairT (rem (Np (Syn.shift p)) (T0 (Syn.shift p))) (Syn.shift p) := by
  simp [Syn.shift]

/-- The remainder of `N_p` by the least period passes the test. -/
theorem s_test {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] Test (rem (Np p) (T0 p)) p ≐ one := by
  refine all_intro eB (.allI (.impI ?_))
  rw [shift_s]
  exact ne_of_one (e_intro (s_point (prime_shift hp).wk (var 0)))

/-- `thm:prime-period`: the least period divides `N_p`. -/
theorem least_dvd {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] dvd (T0 p) (Np p) := by
  have hlt := Prf.andE₂ (div_mod (Γ := Γ) (Np p) (wT p))
  refine .orE (zero_or_succ (rem (Np p) (T0 p))) Prf.hyp0 ?_
  have hs : ((rem (Np p) (T0 p) ≐ succ (pred (rem (Np p) (T0 p)))) :: Γ) ⊢[PRAAx]
      rem (Np p) (T0 p) ≐ succ (pred (rem (Np p) (T0 p))) := Prf.hyp0
  have hl : ((rem (Np p) (T0 p) ≐ succ (pred (rem (Np p) (T0 p)))) :: Γ) ⊢[PRAAx]
      lt (pred (rem (Np p) (T0 p))) (wT p) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (le_congr (congrSucc hs) (.eqRefl _) hlt.wk)
  exact Foundations.BoundedReflection.one_ne_zero _
    (((congrTest hs).eqSymm.eqTrans (s_test hp.wk)).eqSymm.eqTrans (least_minimal hl))

end LeanProofs.IPRA.Combinatorics.BellLeastPeriod
