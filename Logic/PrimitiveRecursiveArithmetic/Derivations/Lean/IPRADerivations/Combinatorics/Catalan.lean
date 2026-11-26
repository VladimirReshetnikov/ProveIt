import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums

/-!
# Catalan numbers

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (Sections 2 and 4: the closed forms (2.4)
and (2.5), the first-order recurrence `thm:ratio-recurrence` and the exact partial sum
`thm:boundary-tail`). With the central binomial coefficient `cb n = C(2n, n)`, the Catalan number
is the quotient `cat n = C(2n, n) / (n + 1)`; it is used through its exactness.

* `cb_fact`: `(2n)! = n! n! C(2n, n)`;
* `cb_rec`: `(n + 1) C(2n + 2, n + 1) = 2 (2n + 1) C(2n, n)`;
* `cat_spec` (2.4): `(n + 1) Cat_n = C(2n, n)`, and `cat_zero`: `Cat_0 = 1`;
* `cat_rec` (`thm:ratio-recurrence`): `(n + 2) Cat_{n+1} = 2 (2n + 1) Cat_n`;
* `cat_odd_binom` (2.5): `(2n + 1) Cat_n = C(2n + 1, n)`;
* `cat_telescope`: `2 Cat_n + C(2n + 2, n + 1) = 4 C(2n, n)`;
* `cat_partial_sum` (`thm:boundary-tail`, cleared of `4^M`):
  `∑_{n<M} Cat_n 4^{M−n} + 2 C(2M, M) = 2 · 4^M`, i.e.
  `∑_{n<M} Cat_n / 4^n = 2 − 2 C(2M, M) / 4^M`.

Each identity is proved multiplied by `n + 1` or by `n! n! (n + 1)` and then cancelled.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Catalan

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_eq mul_cancel catalan_ratio_open)
open LeanProofs.IPRA.Analysis.Products (fact fact_two_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Analysis.PowerSums (mulParam inst2_mulParam sum_mul_param)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

alias succ_pos := Common.succ_pos

/-! ## The central binomial coefficient -/

/-- `C(2n, n)`. -/
abbrev cb (k : PTm n) : PTm n := binom (two * k) k

/-- `(2n)! = n! n! C(2n, n)`. -/
theorem cb_fact (k : PTm n) : Γ ⊢[PRAAx] fact (two * k) ≐ (fact k * fact k) * cb k := by
  have hN : Γ ⊢[PRAAx] two * k ≐ k + k := by ipra_ring
  have g : Γ ⊢[PRAAx] fact (monus (two * k) k) ≐ fact k :=
    congrAp2 factF ((congrMonus hN (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  exact (binom_eq (le_of_eq_add (d := k) hN)).eqTrans (congrMul (congrMul (.eqRefl _) g) (.eqRefl _))

theorem cb_zero : Γ ⊢[PRAAx] cb (zero : PTm n) ≐ one := binom_zero' _

/-- `(n + 1) C(2n + 2, n + 1) = 2 (2n + 1) C(2n, n)`. -/
theorem cb_rec (k : PTm n) : Γ ⊢[PRAAx] succ k * cb (succ k) ≐ (two * succ (two * k)) * cb k := by
  refine mul_cancel (D := fact k * fact k * succ k)
    (pos_mul (pos_mul (fact_pos k) (fact_pos k)) (succ_pos k)) ?_
  ipra_lc natEq (fact_two_succ (Γ := Γ) k) - natEq (cb_fact (Γ := Γ) (succ k)) +
    (2 * 𝔞(k) + 1) * (2 * 𝔞(k) + 2) * natEq (cb_fact (Γ := Γ) k) -
    (𝔞(fact (succ k)) + 𝔞(fact k) * (𝔞(k) + 1)) * 𝔞(cb (succ k)) * natEq (fact_succ (Γ := Γ) k zero)

/-! ## The Catalan numbers -/

/-- `Cat_n = C(2n, n) / (n + 1)`. -/
abbrev cat (k : PTm n) : PTm n := quo (cb k) (succ k)

theorem cat_spec_zero : Γ ⊢[PRAAx] succ (zero : PTm n) * cat zero ≐ cb zero := by
  have q : Γ ⊢[PRAAx] cat (zero : PTm n) ≐ one :=
    quo_of_eq (succ_pos _) (cb_zero.eqTrans (by ipra_ring))
  exact (congrMul (.eqRefl _) q).eqTrans ((by ipra_ring : Γ ⊢[PRAAx] succ zero * one ≐ one).eqTrans
    cb_zero.eqSymm)

/-- `(m + 2) (C(2m + 2, m + 1) ∸ C(2m + 2, m + 2)) = C(2m + 2, m + 1)`. -/
theorem cat_diff (m : PTm n) :
    Γ ⊢[PRAAx] succ (succ m) * monus (cb (succ m)) (binom (two * succ m) (succ (succ m))) ≐ cb (succ m) := by
  have hr : Γ ⊢[PRAAx] succ m * cb (succ m) ≐ succ (succ m) * binom (two * succ m) (succ (succ m)) := by
    have h := inst (Γ := Γ) catalan_ratio_open (![m] : Fin 1 → PTm n)
    simpa using h
  have hC : Γ ⊢[PRAAx] le (binom (two * succ m) (succ (succ m))) (cb (succ m)) := by
    refine mul_le_cancel (d' := succ m) (le_congr hr (.eqRefl _) (le_of_eq_add (d := cb (succ m)) ?_))
    ipra_ring
  ipra_lc natEq hr - (𝔞(m) + 2) * natEq (eq_add_of_le hC)

theorem cat_spec_succ (m : PTm n) : Γ ⊢[PRAAx] succ (succ m) * cat (succ m) ≐ cb (succ m) :=
  (congrMul (.eqRefl _) (quo_of_eq (succ_pos _) (cat_diff m).eqSymm)).eqTrans (cat_diff m)

/-- Variables: `0 = n`. -/
private abbrev specF : Fm PTm 1 := succ (var 0) * cat (var 0) ≐ cb (var 0)

private theorem spec₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] specF := by
  ipra_ind [subst_ap2]
  · exact cat_spec_zero
  · exact cat_spec_succ _

/-- `(n + 1) Cat_n = C(2n, n)`. -/
theorem cat_spec (k : PTm n) : Γ ⊢[PRAAx] succ k * cat k ≐ cb k := by
  have h := inst (Γ := Γ) spec₀ (![k] : Fin 1 → PTm n)
  simpa using h

theorem cat_zero : Γ ⊢[PRAAx] cat (zero : PTm n) ≐ one :=
  quo_of_eq (succ_pos _) (cb_zero.eqTrans (by ipra_ring))

/-- `thm:ratio-recurrence`: `(n + 2) Cat_{n+1} = 2 (2n + 1) Cat_n`. -/
theorem cat_rec (k : PTm n) :
    Γ ⊢[PRAAx] succ (succ k) * cat (succ k) ≐ (two * succ (two * k)) * cat k := by
  refine mul_cancel (D := succ k) (succ_pos k) ?_
  ipra_lc (𝔞(k) + 1) * natEq (cat_spec (Γ := Γ) (succ k)) + natEq (cb_rec (Γ := Γ) k) -
    2 * (2 * 𝔞(k) + 1) * natEq (cat_spec (Γ := Γ) k)

/-- `(2n + 1) Cat_n = C(2n + 1, n)`. -/
theorem cat_odd_binom (k : PTm n) : Γ ⊢[PRAAx] succ (two * k) * cat k ≐ binom (succ (two * k)) k := by
  have hN : Γ ⊢[PRAAx] succ (two * k) ≐ k + succ k := by ipra_ring
  have g : Γ ⊢[PRAAx] fact (monus (succ (two * k)) k) ≐ fact (succ k) :=
    congrAp2 factF ((congrMonus hN (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  have e := natEq ((binom_eq (Γ := Γ) (le_of_eq_add (d := succ k) hN)).eqTrans
    (congrMul (congrMul (.eqRefl _) g) (.eqRefl _)))
  have gg := natEq (fact_succ (Γ := Γ) (two * k) zero); have f₃ := natEq (fact_succ (Γ := Γ) k zero)
  have f₀ := natEq (cb_fact (Γ := Γ) k); have s₀ := natEq (cat_spec (Γ := Γ) k)
  refine mul_cancel (D := fact k * fact k * succ k)
    (pos_mul (pos_mul (fact_pos k) (fact_pos k)) (succ_pos k)) ?_
  ipra_lc 𝔞(fact k) * 𝔞(fact k) * (2 * 𝔞(k) + 1) * s₀ - (2 * 𝔞(k) + 1) * f₀ - gg + e +
    𝔞(fact k) * 𝔞(binom (succ (two * k)) k) * f₃

/-- `2 Cat_n + C(2n + 2, n + 1) = 4 C(2n, n)`. -/
theorem cat_telescope (k : PTm n) : Γ ⊢[PRAAx] two * cat k + cb (succ k) ≐ (two * two) * cb k := by
  refine mul_cancel (D := succ k) (succ_pos k) ?_
  ipra_lc 2 * natEq (cat_spec (Γ := Γ) k) + natEq (cb_rec (Γ := Γ) k)

/-! ## The partial sum of `Cat_n / 4^n` -/

/-- `Cat_j · 4^{M ∸ j}`, with `M` the parameter. -/
abbrev cpB : PTm 2 := cat (var 0) * pw (two * two) (monus (var 1) (var 0))

theorem inst2_cp (j M : PTm n) : inst2 cpB j M = cat j * pw (two * two) (monus M j) := by simp [inst2]

/-- `4^{(M + 1) ∸ j} = 4^{M ∸ j} · 4` for `j ≤ M`. -/
theorem pw_shift {j M : PTm n} (h : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] pw (two * two) (monus (succ M) j) ≐ pw (two * two) (monus M j) * (two * two) := by
  have e : Γ ⊢[PRAAx] succ M ≐ j + succ (monus M j) :=
    (congrSucc (eq_add_of_le h)).eqTrans (add_succ _ _).eqSymm
  exact (congrAp2 powF ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)).eqTrans (pw_succ _ _)

theorem cp_shift_pt {j M : PTm n} (h : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] inst2 cpB j (succ M) ≐ inst2 (mulParam (two * two) cpB) j M := by
  have ec : Syn.subst ![M] (two * two : PTm 1) = two * two := by simp
  rw [inst2_mulParam, ec, inst2_cp, inst2_cp]
  ipra_lc 𝔞(cat j) * natEq (pw_shift (le_of_lt h))

/-- `∑_{j<M} Cat_j 4^{M+1−j} = 4 ∑_{j<M} Cat_j 4^{M−j}`. -/
theorem psum_shift (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF cpB) M (succ M) ≐ (two * two) * ap2 (sumF cpB) M M := by
  have ec : Syn.subst ![M] (two * two : PTm 1) = two * two := by simp
  have s := sum_mul_param (Γ := Γ) (two * two) cpB M M
  rw [ec] at s
  refine (sum_congr_bounded cpB (mulParam (two * two) cpB) (succ M) M M (.allI (.impI ?_))).eqTrans s
  have es : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
  rw [es]
  exact cp_shift_pt Prf.hyp0

theorem psum_step {M : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF cpB) M M + two * cb M ≐ two * pw (two * two) M) :
    Γ ⊢[PRAAx] ap2 (sumF cpB) (succ M) (succ M) + two * cb (succ M) ≐ two * pw (two * two) (succ M) := by
  have e₁ := sum_succ' (Γ := Γ) cpB M (succ M)
  rw [inst2_cp] at e₁
  have p₁ : Γ ⊢[PRAAx] pw (two * two) (monus (succ M) M) ≐ two * two := by
    have e : Γ ⊢[PRAAx] succ M ≐ M + succ zero := by ipra_ring
    refine (congrAp2 powF ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)).eqTrans
      ((pw_succ _ _).eqTrans ((congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _)))
  ipra_lc natEq e₁ + natEq (psum_shift (Γ := Γ) M) + 𝔞(cat M) * natEq p₁ -
    2 * natEq (pw_succ (Γ := Γ) (two * two) M) + 2 * natEq (cat_telescope (Γ := Γ) M) + 4 * natEq ih

/-- Variables: `0 = M`. -/
private abbrev psumF : Fm PTm 1 :=
  ap2 (sumF cpB) (var 0) (var 0) + two * cb (var 0) ≐ two * pw (two * two) (var 0)

private theorem psum₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] psumF := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] natEq (sum_zero (Γ := ([] : List (Fm PTm 0))) cpB zero) +
      2 * natEq (cb_zero (Γ := ([] : List (Fm PTm 0)))) -
      2 * natEq (pw_zero (Γ := ([] : List (Fm PTm 0))) (two * two))
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact psum_step Prf.hyp0

/-- `thm:boundary-tail`: `∑_{j<M} Cat_j 4^{M−j} + 2 C(2M, M) = 2 · 4^M`. -/
theorem cat_partial_sum (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF cpB) M M + two * cb M ≐ two * pw (two * two) M := by
  have h := inst (Γ := Γ) psum₀ (![M] : Fin 1 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.Catalan
