import IPRADerivations.Combinatorics.Fibonacci
import IPRADerivations.AnalyticNumberTheory.PhiUpper

/-!
# Divisibility of Fibonacci numbers and d'Ocagne's identity

Packet: `combinatorics/fibonacci_lucas_ipra` (parity and divisibility theorem, d'Ocagne).

* `fibS_pos`, `fib_pos`: `F_{k+1} ≥ 1`, and `F_k ≥ 1` for `k ≥ 1`;
* `cop_fib`: `gcd(F_k, F_{k+1}) = 1`, since Cassini makes every common divisor divide `1`;
* `fib_dvd_mul`: `F_g ∣ F_{qg}` for `g ≥ 1`;
* `fib_gcd_at`: strong divisibility `gcd(F_m, F_n) = F_{gcd(m, n)}` for `m, n ≥ 1`, from Bézout
  `g + Vn = Um`, the addition law and Gauss's lemma (as for the Pell sequence in `PellGcd`);
* `docagne`: `F_{n+d} F_{n+1} + [n odd] F_d = F_{n+d+1} F_n + [n even] F_d`, i.e.
  `F_m F_{n+1} − F_{m+1} F_n = (−1)^n F_{m−n}` for `m = n + d`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciGcd

open_ipra
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Positivity -/

theorem fibS_pos_step {k : PTm n} (ih : Γ ⊢[PRAAx] fibS k ≐ succ (pred (fibS k))) :
    Γ ⊢[PRAAx] fibS (succ k) ≐ succ (pred (fibS (succ k))) := by
  refine eq_succ_pred (y := pred (fibS k) + fib k) ((fibS_succ k).eqTrans ?_)
  ipra_lc natEq ih

private abbrev posF : Fm PTm 1 := fibS (var 0) ≐ succ (pred (fibS (var 0)))

private theorem pos₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] posF := by
  ipra_ind [subst_fibS]
  · exact eq_succ_pred fibS_zero
  · exact fibS_pos_step Prf.hyp0

/-- `F_{k+1} ≥ 1`. -/
theorem fibS_pos (k : PTm n) : Γ ⊢[PRAAx] fibS k ≐ succ (pred (fibS k)) := by
  have h := inst (Γ := Γ) pos₀ (![k] : Fin 1 → PTm n)
  simpa using h

/-- `F_k ≥ 1` for `k ≥ 1`. -/
theorem fib_pos {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) : Γ ⊢[PRAAx] fib k ≐ succ (pred (fib k)) :=
  eq_succ_pred (((congrFib hk).eqTrans (fib_succ _)).eqTrans (fibS_pos _))

/-! ## Consecutive Fibonacci numbers are coprime -/

section Cop

variable (k : PTm n)

theorem cop_even (h0 : Γ ⊢[PRAAx] par k ≐ zero) : Γ ⊢[PRAAx] gcd (fib k) (fibS k) ≐ one := by
  have hg := gcd_pos_right (a := fib k) (fibS_pos (Γ := Γ) k)
  have d := gcd_dvd_at hg
  have dSS := dvd_mul' hg (fibS k) (Prf.andE₂ d)
  have dFF := dvd_congr (mul_comm _ _) (dvd_mul' hg (fibS (succ k)) (Prf.andE₁ d))
  have e : Γ ⊢[PRAAx] fibS k * fibS k ≐ one + fibS (succ k) * fib k := by
    ipra_lc -natEq (cassini (Γ := Γ) k) + natEq ((congrMonus (.eqRefl one) h0).eqTrans (monus_zero _)) - natEq h0
  exact eq_one_of_dvd_one hg (dvd_sub' hg (dvd_congr e dSS) dFF)

theorem cop_odd (h1 : Γ ⊢[PRAAx] par k ≐ one) : Γ ⊢[PRAAx] gcd (fib k) (fibS k) ≐ one := by
  have hg := gcd_pos_right (a := fib k) (fibS_pos (Γ := Γ) k)
  have d := gcd_dvd_at hg
  have dSS := dvd_mul' hg (fibS k) (Prf.andE₂ d)
  have dFF := dvd_congr (mul_comm _ _) (dvd_mul' hg (fibS (succ k)) (Prf.andE₁ d))
  have e : Γ ⊢[PRAAx] fibS (succ k) * fib k ≐ one + fibS k * fibS k := by
    ipra_lc natEq (cassini (Γ := Γ) k) -
      natEq ((congrMonus (.eqRefl one) h1).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))) + natEq h1
  exact eq_one_of_dvd_one hg (dvd_sub' hg (dvd_congr e dFF) dSS)

/-- `gcd(F_k, F_{k+1}) = 1`. -/
theorem cop_fib : Γ ⊢[PRAAx] gcd (fib k) (fibS k) ≐ one :=
  .orE (par_cases k) (cop_even k Prf.hyp0) (cop_odd k Prf.hyp0)

end Cop

/-! ## `F_g ∣ F_{qg}` -/

theorem dvd_step {q G : PTm n} (hG : Γ ⊢[PRAAx] fib G ≐ succ (pred (fib G)))
    (ih : Γ ⊢[PRAAx] dvd (fib G) (fib (q * G))) : Γ ⊢[PRAAx] dvd (fib G) (fib (succ q * G)) := by
  have e0 : Γ ⊢[PRAAx] succ q * G ≐ q * G + G := by ipra_ring
  refine dvd_congr (congrFib e0).eqSymm (dvd_of_eq' hG
    (w := quo (fib (q * G)) (fib G) * monus (fibS G) (fib G) + fibS (q * G)) ?_)
  ipra_lc natEq (fib_add_sym (Γ := Γ) (q * G) G) +
    (Groth.ι (IPRA.Q.mk Γ (fibS G)) - Groth.ι (IPRA.Q.mk Γ (fib G))) * natEq (eq_of_dvd' hG ih) +
    Groth.ι (IPRA.Q.mk Γ (fib G)) * Groth.ι (IPRA.Q.mk Γ (quo (fib (q * G)) (fib G))) * natEq (eq_add_of_le (fib_le (Γ := Γ) G))

/-- Variables: `0 = q`, `1 = g − 1`. -/
private abbrev dvdF : Fm PTm 2 := dvd (fib (succ (var 1))) (fib (var 0 * succ (var 1)))

private theorem dvd₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] dvdF := by
  ipra_ind [subst_ap2, subst_fib]
  · exact dvd_congr (fib_zero.eqSymm.eqTrans (congrFib (zero_mul _).eqSymm)) (rem_zero _)
  · exact dvd_step (fib_pos (congrSucc (pred_succ _).eqSymm)) Prf.hyp0

/-- `F_g ∣ F_{qg}` for `g ≥ 1`. -/
theorem fib_dvd_mul {g : PTm n} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (q : PTm n) :
    Γ ⊢[PRAAx] dvd (fib g) (fib (q * g)) := by
  have i := inst (Γ := Γ) dvd₀ (![q, pred g] : Fin 2 → PTm n)
  simp at i
  exact dvd_congr_left (congrFib hg.eqSymm) (dvd_congr (congrFib (congrMul (.eqRefl q) hg.eqSymm)) i)

/-! ## Strong divisibility -/

/-- One Bézout branch: `g + V B = U A`, `h ∣ F_A` and `h ∣ F_B` give `h ∣ F_g`. -/
theorem branch {A B g U V h : PTm n} (hh : Γ ⊢[PRAAx] h ≐ succ (pred h))
    (hAp : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hBp : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hA : Γ ⊢[PRAAx] dvd h (fib A)) (hB : Γ ⊢[PRAAx] dvd h (fib B)) (hb : Γ ⊢[PRAAx] g + V * B ≐ U * A) :
    Γ ⊢[PRAAx] dvd h (fib g) := by
  have dUA := dvd_trans' hh (fib_pos hAp) hA (fib_dvd_mul hAp U)
  have dVB := dvd_trans' hh (fib_pos hBp) hB (fib_dvd_mul hBp V)
  have d₁ : Γ ⊢[PRAAx] dvd h (fib (g + V * B)) := dvd_congr (congrFib hb.eqSymm) dUA
  have d₂ : Γ ⊢[PRAAx] dvd h (fib g * fib (V * B)) := dvd_congr (mul_comm _ _) (dvd_mul' hh (fib g) dVB)
  have d₃ : Γ ⊢[PRAAx] dvd h (fibS g * fib (V * B)) := dvd_congr (mul_comm _ _) (dvd_mul' hh (fibS g) dVB)
  have dsum := dvd_congr (fib_add_sym g (V * B)) (dvd_add' hh d₁ d₂)
  have hx := dvd_sub' hh dsum d₃
  have hcop := coprime_dvd_left hh dVB (cop_fib (V * B))
  exact gauss hh hcop (dvd_congr (mul_comm _ _) hx)

/-- `gcd(F_m, F_N) = F_{gcd(m, N)}` for `m, N ≥ 1`. -/
theorem fib_gcd_at {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] gcd (fib m) (fib N) ≐ fib (gcd m N) := by
  have hg := gcd_pos (B := N) hm
  have hYg := fib_pos hg
  have hYm := fib_pos hm
  have dg := gcd_dvd' (b := N) hm
  have em := (eq_of_dvd' hg (Prf.andE₁ dg)).eqTrans (mul_comm _ _)
  have eN := (eq_of_dvd' hg (Prf.andE₂ dg)).eqTrans (mul_comm _ _)
  have dYm := dvd_congr (congrFib em.eqSymm) (fib_dvd_mul hg (quo m (gcd m N)))
  have dYN := dvd_congr (congrFib eN.eqSymm) (fib_dvd_mul hg (quo N (gcd m N)))
  have hh := gcd_pos (B := fib N) hYm
  have hd := gcd_dvd' (b := fib N) hYm
  have l₁ := dvd_le' hYg (gcd_greatest' hYg dYm dYN) hh
  have l₂ : Γ ⊢[PRAAx] dvd (gcd (fib m) (fib N)) (fib (gcd m N)) := by
    refine .orE (bezout_at m N) ?_ ?_
    · exact branch hh.wk hm.wk hN.wk (Prf.andE₁ hd).wk (Prf.andE₂ hd).wk Prf.hyp0
    · exact branch hh.wk hN.wk hm.wk (Prf.andE₂ hd).wk (Prf.andE₁ hd).wk Prf.hyp0
  exact le_antisymm (dvd_le' hh l₂ hYg) l₁

/-- Variables `0 = m − 1`, `1 = n − 1`. -/
abbrev fibGcdFormula : Fm PTm 2 :=
  gcd (fib (succ (var 0))) (fib (succ (var 1))) ≐ fib (gcd (succ (var 0)) (succ (var 1)))

theorem fib_gcd : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 fibGcdFormula :=
  closeUniv 2 (fib_gcd_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm))

/-! ## d'Ocagne's identity -/

theorem doc_step {k d : PTm n}
    (ih : Γ ⊢[PRAAx] fib (k + d) * fibS k + par k * fib d ≐ fibS (k + d) * fib k + monus one (par k) * fib d) :
    Γ ⊢[PRAAx] fib (succ k + d) * fibS (succ k) + par (succ k) * fib d ≐
      fibS (succ k + d) * fib (succ k) + monus one (par (succ k)) * fib d := by
  ipra_lc -natEq ih + Groth.ι (IPRA.Q.mk Γ (fibS (k + d))) * natEq (fibS_succ (Γ := Γ) k) +
    Groth.ι (IPRA.Q.mk Γ (fibS (succ k))) * natEq ((congrFib (Γ := Γ) (succ_add k d)).eqTrans (fib_succ (k + d))) +
    Groth.ι (IPRA.Q.mk Γ (fib d)) * natEq (par_succ (Γ := Γ) k) -
    (Groth.ι (IPRA.Q.mk Γ (fibS (k + d))) + Groth.ι (IPRA.Q.mk Γ (fib (k + d)))) * natEq (fib_succ (Γ := Γ) k) -
    Groth.ι (IPRA.Q.mk Γ (fib (succ k))) * natEq ((congrFibS (Γ := Γ) (succ_add k d)).eqTrans (fibS_succ (k + d))) -
    Groth.ι (IPRA.Q.mk Γ (fib d)) * natEq ((congrMonus (.eqRefl one) (par_succ (Γ := Γ) k)).eqTrans (compl_compl k))

/-- Variables: `0 = n`, `1 = d`. -/
private abbrev docF : Fm PTm 2 :=
  fib (var 0 + var 1) * fibS (var 0) + par (var 0) * fib (var 1) ≐
    fibS (var 0 + var 1) * fib (var 0) + monus one (par (var 0)) * fib (var 1)

private theorem doc₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] docF := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fibS, subst_fib, subst_ap1, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] Groth.ι (IPRA.Q.mk _ (fib (zero + var 0))) * natEq (fibS_zero (Γ := ([] : List (Fm PTm 1)))) +
      natEq (congrFib (Γ := ([] : List (Fm PTm 1))) (zero_add (var 0))) +
      Groth.ι (IPRA.Q.mk _ (fib (var 0))) * natEq (par_zero (Γ := ([] : List (Fm PTm 1)))) -
      Groth.ι (IPRA.Q.mk _ (fibS (zero + var 0))) * natEq (fib_zero (Γ := ([] : List (Fm PTm 1)))) -
      Groth.ι (IPRA.Q.mk _ (fib (var 0))) * natEq ((congrMonus (.eqRefl one) (par_zero (Γ := ([] : List (Fm PTm 1))))).eqTrans (monus_zero _))
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fibS, subst_fib, subst_ap1,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact doc_step Prf.hyp0

/-- d'Ocagne: `F_{k+d} F_{k+1} + [k odd] F_d = F_{k+d+1} F_k + [k even] F_d`. -/
theorem docagne (k d : PTm n) :
    Γ ⊢[PRAAx] fib (k + d) * fibS k + par k * fib d ≐ fibS (k + d) * fib k + monus one (par k) * fib d := by
  have h := inst (Γ := Γ) doc₀ (![k, d] : Fin 2 → PTm n)
  simpa using h

abbrev docagneFormula : Fm PTm 2 :=
  fib (var 0 + var 1) * fibS (var 0) + par (var 0) * fib (var 1) ≐
    fibS (var 0 + var 1) * fib (var 0) + monus one (par (var 0)) * fib (var 1)

theorem docagne_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 docagneFormula := closeUniv 2 (docagne _ _)

end LeanProofs.IPRA.Combinatorics.FibonacciGcd
