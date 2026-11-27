import IPRADerivations.AnalyticNumberTheory.ChebyshevPi

/-!
# The dyadic Chebyshev upper bound for the prime count

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, Theorem `an:chebyshev`,
the upper bound `K π(2^K) ≤ 6 · 2^K`; the same argument is the upper half of the "Integer Chebyshev bounds" of
`analytic-number-theory/prime-counting-ipra` (`sections/growth.tex`).

With `π = PrimeRank.pc` and the primorial `∏_{p ≤ r} p = PrimorialUpper.pri r`:

* `pc_le`: `π(x) ≤ x`;
* `prime_window`: `Y^{π(Y + j)} ≤ Y^{π(Y)} · ∏_{p ≤ Y + j} p` for every `j`: each prime in `(Y, Y + j]` is at least
  `Y` (induction on `j`);
* `window_le`: for `Y ≤ n`, `Y^{π(n)} ≤ Y^{π(Y)} · 4^n` (`PrimorialUpper.pri_le`);
* **`cheb_upper_gen`**: for `2^L ≤ n`, `L π(n) ≤ L π(2^L) + 2n`, and `cheb_upper_gen'` with `π(2^L) ≤ 2^L`;
* `cheb_even`, `cheb_odd`: the cases `K = 2m` (`L = m`) and `K = 2m + 1` (`L = m + 1`), using `m < 2^m`;
* **`cheb_dyadic_upper`**: `K π(2^K) ≤ 6 · 2^K` for every `K`.

With `ChebyshevPi.cheb_dyadic_lower` this is `2^{K−1} ≤ K π(2^K) ≤ 6 · 2^K`.

The Proposition "Integer Chebyshev bounds" of `prime-counting-ipra` in its own form:

* **`cheb_upper_b`**: for `b ≥ 2` and `2^b ≤ N`, `b π(N) ≤ 13 N` (from `cheb_upper_gen` at `L = ⌊b/2⌋`; the
  argument gives `9 N`);
* **`cheb_lower_half`**: for `N < 2^{b+1}`, `⌊N/2⌋ ≤ (b + 1) π(N)`
  (`2^m ≤ C(2m, m) ≤ (2m)^{π(2m)} ≤ N^{π(N)} ≤ 2^{(b+1) π(N)}` at `m = ⌊N/2⌋`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevUpper

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc pc_zero pc_succ pc_step_le congrPc succ_le_succ pc_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper (pri pri_pos pri_succ pri_le congrPri)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevPi (exp_le_of_pw_le cb_lower cb_le_pi)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.Topology.CollisionScales (lt_pw_two)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `π(x) ≤ x` -/

/-- Variable `0 = x`. -/
abbrev pcLeF : Fm PTm 1 := le (pc (var 0)) (var 0)

theorem pc_le_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] pcLeF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr pc_zero.eqSymm (.eqRefl _) (le_refl zero)
  · have ih : [pcLeF] ⊢[PRAAx] le (pc (var 0)) (var 0) := Prf.hyp0
    exact le_trans (pc_step_le (var 0)) (succ_le_succ ih)

/-- `π(x) ≤ x`. -/
theorem pc_le (x : PTm n) : Γ ⊢[PRAAx] le (pc x) x := by
  have i := inst (Γ := Γ) pc_le_open ![x]
  simpa [subst_le, subst_ap2] using i

/-! ## The primes of a window -/

alias mul_pos_ge := WeightedSplit.kle

alias mul_one_r := Common.mul_one_right

theorem assoc_alg (A B C : PTm n) : Γ ⊢[PRAAx] (A * B) * C ≐ A * (B * C) := by
  ipra_ring

/-- One step: from `Y^{π(m)} ≤ Y^{π(Y)} ∏_{p ≤ m} p` and `Y ≤ m + 1` to the same at `m + 1`. -/
theorem window_step {Y m : PTm n} (hY : Γ ⊢[PRAAx] le Y (succ m))
    (ih : Γ ⊢[PRAAx] le (pw Y (pc m)) (pw Y (pc Y) * pri m)) :
    Γ ⊢[PRAAx] le (pw Y (pc (succ m))) (pw Y (pc Y) * pri (succ m)) := by
  have ex : Γ ⊢[PRAAx] pw Y (pc (succ m)) ≐ pw Y (pc m) * pw Y (isP (succ m)) :=
    (congrAp2 powF (pc_succ m) (.eqRefl _)).eqTrans (pw_add _ _ _)
  have fac : Γ ⊢[PRAAx] le (pw Y (isP (succ m))) (pw (succ m) (isP (succ m) * one)) :=
    le_congr (.eqRefl _) (congrAp2 powF (mul_one_r _).eqSymm (.eqRefl _)) (pw_le_pw (isP (succ m)) hY)
  have er : Γ ⊢[PRAAx] (pw Y (pc Y) * pri m) * pw (succ m) (isP (succ m) * one) ≐ pw Y (pc Y) * pri (succ m) :=
    (assoc_alg _ _ _).eqTrans (congrMul (.eqRefl _) (pri_succ m).eqSymm)
  exact le_congr ex.eqSymm er (le_mul_mono ih fac)

/-- `Y^{π(Y + j)} ≤ Y^{π(Y)} · ∏_{p ≤ Y + j} p`. -/
theorem prime_window (Y j : PTm n) : Γ ⊢[PRAAx] le (pw Y (pc (Y + j))) (pw Y (pc Y) * pri (Y + j)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw (Syn.shift Y) (pc (Syn.shift Y + var 0)))
      (pw (Syn.shift Y) (pc (Syn.shift Y)) * pri (Syn.shift Y + var 0))) := by
    ipra_qfind (trivial) [subst_le, subst_ap2]
    · have e0 : Γ ⊢[PRAAx] Y + zero ≐ Y := add_zero Y
      have a : Γ ⊢[PRAAx] le (pw Y (pc Y)) (pw Y (pc Y) * pri Y) := mul_pos_ge (pri_pos Y)
      exact le_congr (congrAp2 powF (congrPc e0.eqSymm) (.eqRefl _)) (congrMul (.eqRefl _) (congrPri e0.eqSymm)) a
    · let D : List (Fm PTm (n + 1)) :=
        le (pw (Syn.shift Y) (pc (Syn.shift Y + var 0)))
          (pw (Syn.shift Y) (pc (Syn.shift Y)) * pri (Syn.shift Y + var 0)) :: Γ.map Fm.shift
      have ih : D ⊢[PRAAx] le (pw (Syn.shift Y) (pc (Syn.shift Y + var 0)))
          (pw (Syn.shift Y) (pc (Syn.shift Y)) * pri (Syn.shift Y + var 0)) := Prf.hyp0
      have es : D ⊢[PRAAx] Syn.shift Y + succ (var 0) ≐ succ (Syn.shift Y + var 0) := add_succ _ _
      have hY : D ⊢[PRAAx] le (Syn.shift Y) (succ (Syn.shift Y + var 0)) :=
        le_trans (le_add_right _ _) (le_succ_self _)
      have st := window_step hY ih
      exact le_congr (congrAp2 powF (congrPc es.eqSymm) (.eqRefl _)) (congrMul (.eqRefl _) (congrPri es.eqSymm)) st
  have r := Prf.allE j hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at r
  exact r

/-- For `Y ≤ N`: `Y^{π(N)} ≤ Y^{π(Y)} · 4^N`. -/
theorem window_le {Y N : PTm n} (h : Γ ⊢[PRAAx] le Y N) :
    Γ ⊢[PRAAx] le (pw Y (pc N)) (pw Y (pc Y) * pw two (two * N)) := by
  have e := eq_add_of_le h
  have w := prime_window (Γ := Γ) Y (monus N Y)
  have w' : Γ ⊢[PRAAx] le (pw Y (pc N)) (pw Y (pc Y) * pri N) :=
    le_congr (congrAp2 powF (congrPc e.eqSymm) (.eqRefl _)) (congrMul (.eqRefl _) (congrPri e.eqSymm)) w
  exact le_trans w' (le_mul_mono (le_refl _) (pri_le N))

/-! ## The general bound -/

/-- For `2^L ≤ N`: `L π(N) ≤ L π(2^L) + 2N`. -/
theorem cheb_upper_gen {L N : PTm n} (h : Γ ⊢[PRAAx] le (pw two L) N) :
    Γ ⊢[PRAAx] le (L * pc N) (L * pc (pw two L) + two * N) := by
  have w := window_le h
  have el : Γ ⊢[PRAAx] pw (pw two L) (pc N) ≐ pw two (L * pc N) := RSA.pw_mul two L (pc N)
  have er : Γ ⊢[PRAAx] pw (pw two L) (pc (pw two L)) * pw two (two * N) ≐
      pw two (L * pc (pw two L) + two * N) :=
    (congrMul (RSA.pw_mul two L (pc (pw two L))) (.eqRefl _)).eqTrans (pw_add _ _ _).eqSymm
  exact exp_le_of_pw_le (le_congr el er w)

theorem add_mono_r {a b c : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (a + c) (b + c) := by
  refine le_of_eq_add (d := monus b a) ?_
  ipra_lc natEq (eq_add_of_le h)

/-- For `2^L ≤ N`: `L π(N) ≤ L 2^L + 2N`. -/
theorem cheb_upper_gen' {L N : PTm n} (h : Γ ⊢[PRAAx] le (pw two L) N) :
    Γ ⊢[PRAAx] le (L * pc N) (L * pw two L + two * N) :=
  le_trans (cheb_upper_gen h) (add_mono_r (le_mul_mono (le_refl L) (pc_le (pw two L))))

/-! ## The dyadic bound -/

theorem even_fin {m P Q T : PTm n} (h : Γ ⊢[PRAAx] le (m * P) (m * Q + two * T))
    (hq : Γ ⊢[PRAAx] le (m * Q) T) : Γ ⊢[PRAAx] le ((two * m) * P) (num 6 * T) := by
  have e1 := natEq (eq_add_of_le h); have e2 := natEq (eq_add_of_le hq)
  refine le_of_eq_add (d := two * monus (m * Q + two * T) (m * P) + two * monus T (m * Q)) ?_
  ipra_lc 2 * e1 + 2 * e2

theorem odd_fin {m P Q T : PTm n} (h : Γ ⊢[PRAAx] le (succ m * P) (succ m * Q + two * T))
    (hq : Γ ⊢[PRAAx] le (succ m * Q) T) : Γ ⊢[PRAAx] le ((two * m + one) * P) (num 6 * T) := by
  have e1 := natEq (eq_add_of_le h); have e2 := natEq (eq_add_of_le hq)
  refine le_of_eq_add (d := two * monus (succ m * Q + two * T) (succ m * P) + two * monus T (succ m * Q) + P) ?_
  ipra_lc 2 * e1 + 2 * e2

theorem dbl (m : PTm n) : Γ ⊢[PRAAx] two * m ≐ m + m := by ipra_ring

theorem odd_split (m : PTm n) : Γ ⊢[PRAAx] two * m + one ≐ succ m + m := by ipra_ring

theorem odd_exp (m : PTm n) : Γ ⊢[PRAAx] m + succ m ≐ two * m + one := by ipra_ring

/-- `K = 2m`: `(2m) π(2^{2m}) ≤ 6 · 2^{2m}`. -/
theorem cheb_even (m : PTm n) :
    Γ ⊢[PRAAx] le ((two * m) * pc (pw two (two * m))) (num 6 * pw two (two * m)) := by
  have hm : Γ ⊢[PRAAx] le m (two * m) := le_of_eq_add (d := m) (dbl m)
  have hY : Γ ⊢[PRAAx] le (pw two m) (pw two (two * m)) := PowerCleared.pw_le_exp two_pos' hm
  have g := cheb_upper_gen' hY
  have lm : Γ ⊢[PRAAx] le m (pw two m) := le_of_lt (lt_pw_two m)
  have sq : Γ ⊢[PRAAx] pw two m * pw two m ≐ pw two (two * m) :=
    (pw_add two m m).eqSymm.eqTrans (congrAp2 powF (dbl m).eqSymm (.eqRefl _))
  have hq : Γ ⊢[PRAAx] le (m * pw two m) (pw two (two * m)) :=
    le_congr (.eqRefl _) sq (le_mul_mono lm (le_refl (pw two m)))
  exact even_fin g hq

/-- `K = 2m + 1`: `(2m + 1) π(2^{2m+1}) ≤ 6 · 2^{2m+1}`. -/
theorem cheb_odd (m : PTm n) :
    Γ ⊢[PRAAx] le ((two * m + one) * pc (pw two (two * m + one))) (num 6 * pw two (two * m + one)) := by
  have hm : Γ ⊢[PRAAx] le (succ m) (two * m + one) := le_of_eq_add (d := m) (odd_split m)
  have hY : Γ ⊢[PRAAx] le (pw two (succ m)) (pw two (two * m + one)) := PowerCleared.pw_le_exp two_pos' hm
  have g := cheb_upper_gen' hY
  have lm : Γ ⊢[PRAAx] le (succ m) (pw two m) := lt_pw_two m
  have sq : Γ ⊢[PRAAx] pw two m * pw two (succ m) ≐ pw two (two * m + one) :=
    (pw_add two m (succ m)).eqSymm.eqTrans (congrAp2 powF (odd_exp m) (.eqRefl _))
  have hq : Γ ⊢[PRAAx] le (succ m * pw two (succ m)) (pw two (two * m + one)) :=
    le_congr (.eqRefl _) sq (le_mul_mono lm (le_refl (pw two (succ m))))
  exact odd_fin g hq

/-- **`an:chebyshev`, the upper bound**: `K π(2^K) ≤ 6 · 2^K` for every `K`. -/
theorem cheb_dyadic_upper (K : PTm n) : Γ ⊢[PRAAx] le (K * pc (pw two K)) (num 6 * pw two K) := by
  refine .orE (even_or_odd K) ?_ ?_
  · have e : ((K ≐ two * half K) :: Γ) ⊢[PRAAx] K ≐ two * half K := Prf.hyp0
    have p : ((K ≐ two * half K) :: Γ) ⊢[PRAAx] pw two (two * half K) ≐ pw two K :=
      congrAp2 powF e.eqSymm (.eqRefl _)
    exact le_congr (congrMul e.eqSymm (congrPc p)) (congrMul (.eqRefl _) p) (cheb_even (half K))
  · have e : ((K ≐ two * half K + one) :: Γ) ⊢[PRAAx] K ≐ two * half K + one := Prf.hyp0
    have p : ((K ≐ two * half K + one) :: Γ) ⊢[PRAAx] pw two (two * half K + one) ≐ pw two K :=
      congrAp2 powF e.eqSymm (.eqRefl _)
    exact le_congr (congrMul e.eqSymm (congrPc p)) (congrMul (.eqRefl _) p) (cheb_odd (half K))

/-! ## The integer Chebyshev bounds of `prime-counting-ipra` -/

theorem thirteen_alg {b h P Q N : PTm n} (g : Γ ⊢[PRAAx] le (h * P) (h * Q + two * N))
    (hq : Γ ⊢[PRAAx] le (h * Q) N) (hb3 : Γ ⊢[PRAAx] le b (num 3 * h)) :
    Γ ⊢[PRAAx] le (b * P) (num 13 * N) := by
  have e1 := natEq (eq_add_of_le g); have e2 := natEq (eq_add_of_le hq); have e3 := natEq (eq_add_of_le hb3)
  refine le_of_eq_add (d := num 4 * N + num 3 * monus (h * Q + two * N) (h * P) + num 3 * monus N (h * Q) +
    monus (num 3 * h) b * P) ?_
  ipra_lc 3 * e1 + 3 * e2 + 𝔞 P * e3

/-- `b = 2h + r`, `r ≤ 1` and `b ≥ 2` give `b ≤ 3h`. -/
theorem le_three_half {b h r : PTm n} (e : Γ ⊢[PRAAx] b ≐ two * h + r) (hr : Γ ⊢[PRAAx] le r one)
    (hb : Γ ⊢[PRAAx] le two b) : Γ ⊢[PRAAx] le b (num 3 * h) := by
  refine .orE (zero_or_succ h) ?_ ?_
  · -- `h = 0`: then `b = r ≤ 1`, against `b ≥ 2`
    have h0 : ((h ≐ zero) :: Γ) ⊢[PRAAx] h ≐ zero := Prf.hyp0
    have br : ((h ≐ zero) :: Γ) ⊢[PRAAx] b ≐ r := by
      have ew : ((h ≐ zero) :: Γ) ⊢[PRAAx] b ≐ two * h + r := e.wk
      ipra_lc natEq ew + 2 * natEq h0
    have l : ((h ≐ zero) :: Γ) ⊢[PRAAx] lt one r := le_congr (.eqRefl _) br hb.wk
    exact le_lt_absurd _ hr.wk l
  · have hp : ((h ≐ succ (pred h)) :: Γ) ⊢[PRAAx] h ≐ succ (pred h) := Prf.hyp0
    have ew : ((h ≐ succ (pred h)) :: Γ) ⊢[PRAAx] b ≐ two * h + r := e.wk
    have hrw : ((h ≐ succ (pred h)) :: Γ) ⊢[PRAAx] le r one := hr.wk
    have a := natEq ew; have c := natEq hp; have s := natEq (eq_add_of_le hrw)
    refine le_of_eq_add (d := pred h + monus one r) ?_
    ipra_lc -a + c + s

theorem half_alg {b h r : PTm n} (e : Γ ⊢[PRAAx] b ≐ two * h + r) : Γ ⊢[PRAAx] b ≐ (h + h) + r := by
  ipra_lc natEq e

/-- **Upper half**: for `b ≥ 2` and `2^b ≤ N`, `b π(N) ≤ 13 N`. -/
theorem cheb_upper_b {b N : PTm n} (hb : Γ ⊢[PRAAx] le two b) (hN : Γ ⊢[PRAAx] le (pw two b) N) :
    Γ ⊢[PRAAx] le (b * pc N) (num 13 * N) := by
  have e := half_par (Γ := Γ) b
  have e' := half_alg e
  have hr : Γ ⊢[PRAAx] le (par b) one :=
    .orE (par_cases b) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le one))
      (le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl one))
  have hhb : Γ ⊢[PRAAx] le (half b + half b) b := le_of_eq_add e'
  have hh : Γ ⊢[PRAAx] le (half b) b := le_trans (le_add_right _ _) hhb
  have y1 : Γ ⊢[PRAAx] le (pw two (half b)) N := le_trans (PowerCleared.pw_le_exp two_pos' hh) hN
  have g := cheb_upper_gen' y1
  have lm : Γ ⊢[PRAAx] le (half b) (pw two (half b)) := le_of_lt (lt_pw_two (half b))
  have sq : Γ ⊢[PRAAx] le (pw two (half b) * pw two (half b)) N :=
    le_congr (pw_add two (half b) (half b)) (.eqRefl _) (le_trans (PowerCleared.pw_le_exp two_pos' hhb) hN)
  have hq : Γ ⊢[PRAAx] le (half b * pw two (half b)) N :=
    le_trans (le_mul_mono lm (le_refl (pw two (half b)))) sq
  exact thirteen_alg g hq (le_three_half e hr hb)

theorem two_half_le (N : PTm n) : Γ ⊢[PRAAx] le (two * half N) N := le_of_eq_add (half_par N)

theorem one_le_double {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] le one (two * m) := by
  refine le_of_eq_add (d := two * pred m + one) ?_
  ipra_lc 2 * natEq hm

/-- **Lower half**, in the packet's form: for `N < 2^{b+1}`, `⌊N/2⌋ ≤ (b + 1) π(N)`. -/
theorem cheb_lower_half {N b : PTm n} (hb : Γ ⊢[PRAAx] lt N (pw two (succ b))) :
    Γ ⊢[PRAAx] le (half N) (succ b * pc N) := by
  refine .orE (zero_or_succ (half N)) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)) ?_
  let C : List (Fm PTm n) := (half N ≐ succ (pred (half N))) :: Γ
  have mpos : C ⊢[PRAAx] half N ≐ succ (pred (half N)) := Prf.hyp0
  have l2 : C ⊢[PRAAx] le (two * half N) N := two_half_le N
  have Npos : C ⊢[PRAAx] N ≐ succ (pred N) := BinomialThree.pos_of_one_le (le_trans (one_le_double mpos) l2)
  have c1 := cb_lower (Γ := C) (half N)
  have c2 := cb_le_pi mpos
  have c3 : C ⊢[PRAAx] le (pw (two * half N) (pc (two * half N))) (pw N (pc (two * half N))) :=
    pw_le_pw (pc (two * half N)) l2
  have c4 : C ⊢[PRAAx] le (pw N (pc (two * half N))) (pw N (pc N)) :=
    PowerCleared.pw_le_exp Npos (pc_mono l2)
  have c5 : C ⊢[PRAAx] le (pw N (pc N)) (pw (pw two (succ b)) (pc N)) := pw_le_pw (pc N) (le_of_lt hb.wk)
  have r : C ⊢[PRAAx] pw (pw two (succ b)) (pc N) ≐ pw two (succ b * pc N) := RSA.pw_mul two (succ b) (pc N)
  exact exp_le_of_pw_le (le_congr (.eqRefl _) r (le_trans c1 (le_trans c2 (le_trans c3 (le_trans c4 c5)))))

end LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevUpper
