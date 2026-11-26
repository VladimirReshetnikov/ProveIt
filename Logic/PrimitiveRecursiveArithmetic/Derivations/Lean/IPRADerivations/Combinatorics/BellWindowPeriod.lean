import IPRADerivations.Combinatorics.BellModularRecurrence
import IPRADerivations.Combinatorics.BellLeastPeriod

/-!
# A matching window is a period of the Bell numbers modulo `m` (`bell_numbers_ipra`, `thm:all-moduli-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:all-moduli-period`. With the state vector `v_n = (B_n, …, B_{n+m−1}) mod m`: "Therefore
`T = b − a` is a period from the start; the forward recurrence proves `v_{n+T} = v_n` for
every `n`."

For every modulus `m ≥ 1` and every `t`, with the bit `Test t m` of the `m` congruences
`B_{t+i} ≡ B_i (mod m)`, `i < m` (`v_t = v_0`; the bit of `Combinatorics/BellLeastPeriod`,
whose definition does not use primality):

* `mid_pt`, `window_case`: an index `N ≥ m` is reached from the `m` preceding indices by
  `recurrence_split` at `t + (N − m)` and at `N − m`: the middle sums are congruent term by
  term and cancel;
* `window_step`, `window_all`, `period_of_window`: `Test t m` gives `B_{t+N} ≡ B_N (mod m)`
  for every `N`. The propagation is a course-of-values induction through one bit;
* `window_mul`: then every multiple `q t` is a period.

Not derived: the existence of a matching window `t ≤ m^m` (the pigeonhole collision of two
state vectors and the backward recurrence), hence the uniform period `(m^m)!`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellWindowPeriod

open_ipra
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (cong_add cong_mul cong_of_eq cong_sum
  shift_pair shift_add shift_monus)
open LeanProofs.IPRA.Combinatorics.BellPrimePeriod (cong_cancel)
open LeanProofs.IPRA.Combinatorics.BellPeriodNp (bellB inst2_bellB shift_zero)
open LeanProofs.IPRA.Combinatorics.BellModularRecurrence (recurrence_split MidB)
open LeanProofs.IPRA.Combinatorics.BellLeastPeriod (eB e_elim e_intro Test allB_extend)
open LeanProofs.IPRA.Combinatorics.LinearFactorTable (cyc actB act_at)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB allB_zero all_elim)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One index from the `m` preceding ones -/

theorem sh_at (K m c : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody (actB bellB)) K (LinearFactorTable.par m c zero) ≐
      cyc m (succ K) * bell (c + succ K) := by
  rw [inst2_shiftBody]
  have a := act_at (Γ := Γ) bellB (succ K) m c zero
  rw [inst2_bellB] at a
  exact a

/-- The middle terms at `t + (N − m)` and at `N − m` are congruent. -/
theorem mid_pt {t m N K : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hQ : Γ ⊢[PRAAx] allB eB N (pairT t m) ≐ one) (hle : Γ ⊢[PRAAx] le m N)
    (hK : Γ ⊢[PRAAx] lt K (pred m)) :
    Γ ⊢[PRAAx]
      rem (inst2 (shiftBody (actB bellB)) K (LinearFactorTable.par m (t + monus N m) zero)) m ≐
        rem (inst2 (shiftBody (actB bellB)) K (LinearFactorTable.par m (monus N m) zero)) m := by
  have hlt : Γ ⊢[PRAAx] lt (monus N m + succ K) N := by
    refine le_of_eq_add (d := monus (pred m) (succ K)) ?_
    have a := natEq (eq_add_of_le hle)
    have b := natEq hm
    have c := natEq (eq_add_of_le hK)
    apply deriveNat; ipra_simps
    linear_combination a + b + c
  have h : Γ ⊢[PRAAx] rem (bell (t + monus N m + succ K)) m ≐
      rem (bell (monus N m + succ K)) m :=
    (cong_of_eq (congrBell (a := t + monus N m + succ K) (b := t + (monus N m + succ K))
      (by ipra_ring))).eqTrans (e_elim (all_elim eB hQ hlt))
  exact (cong_of_eq (sh_at K m (t + monus N m))).eqTrans
    ((cong_mul (cyc m (succ K)) hm h).eqTrans (cong_of_eq (sh_at K m (monus N m))).eqSymm)

/-- An index `N ≥ m`. -/
theorem window_case {t m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hQ : Γ ⊢[PRAAx] allB eB N (pairT t m) ≐ one) (hle : Γ ⊢[PRAAx] le m N) :
    Γ ⊢[PRAAx] rem (bell (t + N)) m ≐ rem (bell N) m := by
  have eN := eq_add_of_le hle
  have lt0 : Γ ⊢[PRAAx] lt (monus N m) N := by
    refine le_of_eq_add (d := pred m) ?_
    have a := natEq eN
    have b := natEq hm
    apply deriveNat; ipra_simps
    linear_combination a + b
  have c0 := e_elim (all_elim eB hQ lt0)
  have r1 := recurrence_split hm (t + monus N m)
  have r0 := recurrence_split hm (monus N m)
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
    simpa [Fm.shift, Syn.shift] using hm.shift
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
      allB eB (Syn.shift N) (pairT (Syn.shift t) (Syn.shift m)) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  have hle' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift m) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hle.shift
  have e : Syn.shift (pred m) = pred (Syn.shift m) := by simp [Syn.shift]
  have mid : Γ ⊢[PRAAx] rem (MidB m (t + monus N m)) m ≐ rem (MidB m (monus N m)) m :=
    cong_sum (shiftBody (actB bellB)) (shiftBody (actB bellB)) hm (.allI (.impI (by
      simp only [shift_pair, shift_add, shift_monus, shift_zero]
      exact mid_pt hm'.wk hQ'.wk hle'.wk (by rw [← e]; exact Prf.hyp0))))
  have key : Γ ⊢[PRAAx]
      rem (MidB m (t + monus N m) + bell (t + monus N m + m)) m ≐
        rem (MidB m (t + monus N m) + bell (monus N m + m)) m :=
    (cong_of_eq (add_comm _ _)).eqTrans (r1.eqTrans (c0.eqTrans (r0.eqSymm.eqTrans
      ((cong_add hm (.eqRefl _) mid.eqSymm).eqTrans (cong_of_eq (add_comm _ _))))))
  have e₁ : Γ ⊢[PRAAx] t + N ≐ t + monus N m + m := by
    have a := natEq eN
    apply deriveNat; ipra_simps
    linear_combination a
  have e₂ : Γ ⊢[PRAAx] monus N m + m ≐ N := by
    have a := natEq eN
    apply deriveNat; ipra_simps
    linear_combination -a
  exact (cong_of_eq (congrBell e₁)).eqTrans
    ((cong_cancel hm key).eqTrans (cong_of_eq (congrBell e₂)))

/-! ## Propagation -/

theorem window_step {t m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hT : Γ ⊢[PRAAx] Test t m ≐ one) (hQ : Γ ⊢[PRAAx] allB eB N (pairT t m) ≐ one) :
    Γ ⊢[PRAAx] allB eB (succ N) (pairT t m) ≐ one :=
  allB_extend eB hQ (e_intro (.orE (lt_or_le N m)
    (e_elim (all_elim eB hT.wk Prf.hyp0)) (window_case hm.wk hQ.wk Prf.hyp0)))

/-- The induction formula; variable `0` is the number of indices reached. -/
abbrev propF (t m : PTm n) : Fm PTm (n + 1) :=
  allB eB (var 0) (pairT (Syn.shift t) (Syn.shift m)) ≐ one

theorem window_all {t m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hT : Γ ⊢[PRAAx] Test t m ≐ one) (N : PTm n) :
    Γ ⊢[PRAAx] allB eB N (pairT t m) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (propF t m) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using allB_zero (Γ := Γ) eB (pairT t m)
    · have hT' : (Γ.map Fm.shift) ⊢[PRAAx] Test (Syn.shift t) (Syn.shift m) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hT.shift
      have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
        simpa [Fm.shift, Syn.shift] using hm.shift
      have st : (propF t m :: Γ.map Fm.shift) ⊢[PRAAx]
          allB eB (succ (var 0)) (pairT (Syn.shift t) (Syn.shift m)) ≐ one :=
        window_step hm'.wk hT'.wk Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE N hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- `thm:all-moduli-period`, forward propagation: a matching window is a period at every
index, `B_{t+N} ≡ B_N (mod m)`. -/
theorem period_of_window {t m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hT : Γ ⊢[PRAAx] Test t m ≐ one) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (t + N)) m ≐ rem (bell N) m :=
  e_elim (all_elim eB (window_all hm hT (succ N)) (le_refl (succ N)))

/-- The induction formula of `window_mul`; variable `0` is the multiplier. -/
abbrev mulF (t m N : PTm n) : Fm PTm (n + 1) :=
  rem (bell (var 0 * Syn.shift t + Syn.shift N)) (Syn.shift m) ≐
    rem (bell (Syn.shift N)) (Syn.shift m)

/-- Every multiple of a period is a period. -/
theorem window_mul {t m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hT : Γ ⊢[PRAAx] Test t m ≐ one) (q N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (q * t + N)) m ≐ rem (bell N) m := by
  have hall : Γ ⊢[PRAAx] Fm.all (mulF t m N) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] rem (bell (zero * t + N)) m ≐ rem (bell N) m :=
        cong_of_eq (congrBell (by ipra_ring))
      simpa using b
    · have hT' : (Γ.map Fm.shift) ⊢[PRAAx] Test (Syn.shift t) (Syn.shift m) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hT.shift
      have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
        simpa [Fm.shift, Syn.shift] using hm.shift
      have st : (mulF t m N :: Γ.map Fm.shift) ⊢[PRAAx]
          rem (bell (succ (var 0) * Syn.shift t + Syn.shift N)) (Syn.shift m) ≐
            rem (bell (Syn.shift N)) (Syn.shift m) :=
        (cong_of_eq (congrBell (a := succ (var 0) * Syn.shift t + Syn.shift N)
          (b := Syn.shift t + (var 0 * Syn.shift t + Syn.shift N))
          (by ipra_ring))).eqTrans
          ((period_of_window hm'.wk hT'.wk _).eqTrans Prf.hyp0)
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE q hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

end LeanProofs.IPRA.Combinatorics.BellWindowPeriod
