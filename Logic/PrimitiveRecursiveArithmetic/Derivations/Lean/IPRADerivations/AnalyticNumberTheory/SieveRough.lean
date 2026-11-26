import IPRADerivations.AnalyticNumberTheory.DivisorExchange
import IPRADerivations.AnalyticNumberTheory.SymmetryInstances
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.Header

/-!
# Numbers without small divisors: a weighted divisor sum collapses to its first term

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-majorant`:
"If `gcd(n, P) = 1`, only `d = 1` occurs, so both sides equal one."

Here the condition is "no `d` with `2 ≤ d < Z` divides `m`" (in particular every prime `m ≥ Z` satisfies it):

* `rB`, `rgh`: the body `[d ≥ 2][d ∣ m]` and the indicator `rgh Z m = [Σ_{d<Z} [d ≥ 2][d ∣ m] = 0]`;
* `no_div`: if that sum vanishes, then `[d ∣ m] = 0` for `2 ≤ d < Z` (a summand is at most the sum,
  `term_le_sum`);
* `rough_pt`: for such `m`, a body `u` with `u(0) = 0` and `d < Z`: `[d ∣ m] u(d) = [d = 1] u(d)`;
* `rough_sum`: `Σ_{d<Z} [d ∣ m] u(d) = u(1)` for `Z ≥ 2` (`Core/Fubini.sum_delta`).

The sieve weights `λ_d = d · …` vanish at `d = 0`, so their divisor sums at such `m` are `λ_1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveRough

open_ipra
open LeanProofs.IPRA.Signum (sg sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange (dvB dvB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (rem_one shift_one'')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (one_le_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The indicator of having no divisor in `[2, Z)` -/

/-- `[d ≥ 2][d ∣ m]` over `0 = d`, `1 = m`. -/
abbrev rB : PTm 2 := sg (monus (var 0) one) * eqb (rem (var 1) (var 0)) zero

theorem inst2_rB (d m : PTm n) : inst2 rB d m = sg (monus d one) * eqb (rem m d) zero := by simp [inst2]

/-- `[no d with 2 ≤ d < Z divides m]`. -/
abbrev rgh (Z m : PTm n) : PTm n := eqb (ap2 (sumF rB) Z m) zero

/-- `[d ≥ 2] = 1` for `d ≥ 2`. -/
theorem two_le_sg {d : PTm n} (h2 : Γ ⊢[PRAAx] le two d) : Γ ⊢[PRAAx] sg (monus d one) ≐ one := by
  have e : Γ ⊢[PRAAx] d ≐ succ (succ (monus d two)) :=
    (eq_add_of_le h2).eqTrans (by ipra_ring)
  have m1 : Γ ⊢[PRAAx] monus d one ≐ succ (monus d two) :=
    (congrMonus e (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))
  exact (congrSg m1).eqTrans (sg_succ _)

/-- If no `d` with `2 ≤ d < Z` divides `m`, then `[d ∣ m] = 0` for each such `d`. -/
theorem no_div {Z m d : PTm n} (hr : Γ ⊢[PRAAx] ap2 (sumF rB) Z m ≐ zero) (hd : Γ ⊢[PRAAx] lt d Z)
    (h2 : Γ ⊢[PRAAx] le two d) : Γ ⊢[PRAAx] eqb (rem m d) zero ≐ zero := by
  have t := term_le_sum rB (x := m) hd
  rw [inst2_rB] at t
  have z : Γ ⊢[PRAAx] sg (monus d one) * eqb (rem m d) zero ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) hr t) (zero_le _)
  exact (one_mul _).eqSymm.eqTrans ((congrMul (two_le_sg h2).eqSymm (.eqRefl _)).eqTrans z)

/-- `d ≥ 1` and `d ≠ 1` give `d ≥ 2`. -/
theorem two_le_of {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hne : Γ ⊢[PRAAx] neg (d ≐ one)) :
    Γ ⊢[PRAAx] le two d := by
  refine .orE (lt_or_le d two) ?_ Prf.hyp0
  have h1 : (lt d two :: Γ) ⊢[PRAAx] le d one := (succ_monus_succ d one).eqSymm.eqTrans Prf.hyp0
  have h2 : (lt d two :: Γ) ⊢[PRAAx] le one d := one_le_pos (hd.wk (ψ := lt d two))
  exact .botE _ (Prf.impE (hne.wk (ψ := lt d two)) (le_antisymm h1 h2))

/-! ## The divisor sum at such a number -/

/-- For `d < Z`: `[d ∣ m] u(d) = [d = 1] u(d)`, as summands of a divisor sum and of a delta sum. -/
theorem rough_pt (u : PTm 2) {Z m y d : PTm n} (hz : Γ ⊢[PRAAx] inst2 u zero y ≐ zero)
    (hr : Γ ⊢[PRAAx] ap2 (sumF rB) Z m ≐ zero) (hd : Γ ⊢[PRAAx] lt d Z) :
    Γ ⊢[PRAAx] inst2 (dvB u) d (pairT m y) ≐ inst2 (dB u) d (pairT one y) := by
  have eD : Γ ⊢[PRAAx] inst2 (dB u) d (pairT one y) ≐ eqb one d * inst2 u d y := by
    rw [inst2_dB]
    exact congrMul (congrEqb' (fst_pair _ _) (.eqRefl _)) (congrInst2 u (.eqRefl _) (snd_pair _ _))
  refine (dvB_at u d m y).eqTrans (Prf.eqTrans ?_ eD.eqSymm)
  refine .orE (zero_or_succ d) ?_ ?_
  · have u0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] inst2 u d y ≐ zero :=
      (congrInst2 u Prf.hyp0 (.eqRefl _)).eqTrans (hz.wk (ψ := d ≐ zero))
    exact ((congrMul (.eqRefl _) u0).eqTrans (mul_zero _)).eqTrans
      ((congrMul (.eqRefl _) u0).eqTrans (mul_zero _)).eqSymm
  · refine .orE (eq_or_ne d one) ?_ ?_
    · let C : List (Fm PTm n) := (d ≐ one) :: (d ≐ succ (pred d)) :: Γ
      have h1 : C ⊢[PRAAx] d ≐ one := Prf.hyp0
      have e1 : C ⊢[PRAAx] eqb (rem m d) zero ≐ one :=
        (congrEqb' (congrAp2 remF (.eqRefl _) h1) (.eqRefl _)).eqTrans (eqb_of_eq (rem_one m))
      have e2 : C ⊢[PRAAx] eqb one d ≐ one := eqb_of_eq h1.eqSymm
      exact congrMul (e1.eqTrans e2.eqSymm) (.eqRefl _)
    · let C : List (Fm PTm n) := neg (d ≐ one) :: (d ≐ succ (pred d)) :: Γ
      have hne : C ⊢[PRAAx] neg (d ≐ one) := Prf.hyp0
      have hd1 : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
      have h2 : C ⊢[PRAAx] le two d := two_le_of hd1 hne
      have z1 : C ⊢[PRAAx] eqb (rem m d) zero ≐ zero := no_div hr.wk.wk hd.wk.wk h2
      have hne' : C ⊢[PRAAx] neg (one ≐ d) := .impI (Prf.impE hne.wk (Prf.hyp0 : ((one ≐ d) :: C) ⊢[PRAAx] one ≐ d).eqSymm)
      have z2 : C ⊢[PRAAx] eqb one d ≐ zero := eqb_of_ne hne'
      exact (zero_mul_l z1 _).eqTrans (zero_mul_l z2 _).eqSymm

/-- For `Z ≥ 2`, a body with `u(0) = 0` and `m` without divisors in `[2, Z)`:
`Σ_{d<Z} [d ∣ m] u(d) = u(1)`. -/
theorem rough_sum (u : PTm 2) (hz : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (y : PTm k), Δ ⊢[PRAAx] inst2 u zero y ≐ zero)
    {Z m y : PTm n} (hZ : Γ ⊢[PRAAx] lt one Z) (hr : Γ ⊢[PRAAx] ap2 (sumF rB) Z m ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (dvB u)) Z (pairT m y) ≐ inst2 u one y := by
  have hr' : (Γ.map Fm.shift) ⊢[PRAAx] ap2 (sumF rB) (Syn.shift Z) (Syn.shift m) ≐ zero := by
    have h := hr.shift
    simp only [Fm.shift, Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_zero] at h
    exact h
  have c : Γ ⊢[PRAAx] ap2 (sumF (dvB u)) Z (pairT m y) ≐ ap2 (sumF (dB u)) Z (pairT one y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, shift_one'']
    exact rough_pt u (hz _) hr'.wk Prf.hyp0
  exact c.eqTrans (sum_delta u hZ)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveRough
