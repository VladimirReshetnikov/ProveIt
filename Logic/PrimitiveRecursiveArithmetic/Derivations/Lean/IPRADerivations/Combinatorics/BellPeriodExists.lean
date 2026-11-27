import IPRADerivations.Combinatorics.BellWindowBackward
import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Foundations.TermCompiler
import IPRADerivations.Topology.InjectionBound
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.AnalyticNumberTheory.Primes

/-!
# The Bell numbers are periodic modulo every `m` (`bell_numbers_ipra`, `thm:all-moduli-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:all-moduli-period`: "For every integer `m ≥ 1`, the Bell sequence is purely periodic
modulo `m`. There is a period `T` with `1 ≤ T ≤ m^m`, found by a bounded computation. In
particular the following uniform period is valid: `B_{n+(m^m)!} ≡ B_n (mod m)` (`n ≥ 0`)."
Proof: "Its state vector is `v_n = (B_n, …, B_{n+m−1}) mod m`, an element of a list of `m^m`
states. ... Among `v_0, …, v_{m^m}` two states agree, by the finite pigeonhole principle. ...
`T = b − a` is a period from the start ... Since every positive integer at most `m^m` divides
`(m^m)!`, repeating the period proves (all-moduli-period)."

* `code i m`: the state `v_i` as a base-`m` number, `∑_{k<m} (B_{i+k} mod m) m^k`
  (`Foundations/MixedRadix`), below `m^m` (`code_bound`);
* `digit_eq`, `collision_window`: equal codes have equal digits, so `v_a = v_b`
  (`MixedRadix.decode`);
* `ia m`, `ib m`: the first collision `a < b ≤ m^m` among the `m^m + 1` codes, by the pair
  search of `Topology/InjectionBound`; `Tm m = b − a`;
* `period_test`, `period_pos`, `period_le`: `1 ≤ T ≤ m^m` and `v_T = v_0`
  (`Combinatorics/BellWindowBackward.window_back`);
* `bell_period_mod`: `B_{T+N} ≡ B_N (mod m)` for every `N`
  (`Combinatorics/BellWindowPeriod.period_of_window`);
* `bell_uniform_period`: `B_{(m^m)!+N} ≡ B_N (mod m)` for every `N`;
  `bell_uniform_period_closed`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellPeriodExists

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (cong_of_eq shift_pair shift_pw)
open LeanProofs.IPRA.Combinatorics.BellLeastPeriod (Test ne_of_one)
open LeanProofs.IPRA.Combinatorics.BellWindowPeriod (period_of_window window_mul)
open LeanProofs.IPRA.Combinatorics.BellWindowBackward (wB wpar w_intro W congrW shift_wpar
  window_back)
open LeanProofs.IPRA.Foundations.MixedRadix (Pl Cd code_lt decode)
open LeanProofs.IPRA.Foundations.TermCompiler (symbol symbol_inst2)
open LeanProofs.IPRA.Foundations.BoundedReflection (all_intro)
open LeanProofs.IPRA.Topology.InjectionBound (rangeBelow collision)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiPigeonhole (first second)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The state code -/

/-- The radix `m`, over `0 = k`, `1 = ⟨i, m⟩`. -/
abbrev rS : PTm 2 := sndT (var 1)

/-- The digit `B_{i+k} mod m`, over `0 = k`, `1 = ⟨i, m⟩`. -/
abbrev dS : PTm 2 := rem (bell (fstT (var 1) + var 0)) (sndT (var 1))

theorem r_at (k i m : PTm n) : Γ ⊢[PRAAx] inst2 rS k (pairT i m) ≐ m := by
  have h : inst2 rS k (pairT i m) = sndT (pairT i m) := by simp [inst2]
  rw [h]
  exact snd_pair _ _

theorem d_at (k i m : PTm n) :
    Γ ⊢[PRAAx] inst2 dS k (pairT i m) ≐ rem (bell (i + k)) m := by
  have h : inst2 dS k (pairT i m) =
      rem (bell (fstT (pairT i m) + k)) (sndT (pairT i m)) := by simp [inst2]
  rw [h]
  exact congrAp2 remF (congrBell (congrAdd (fst_pair _ _) (.eqRefl _))) (snd_pair _ _)

theorem dig_lt {k i m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] lt (inst2 dS k (pairT i m)) (inst2 rS k (pairT i m)) :=
  lt_congr (d_at k i m).eqSymm (r_at k i m).eqSymm (rem_lt' hm _)

theorem dig_all {i m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      lt (inst2 dS (var 0) (Syn.shift (pairT i m))) (inst2 rS (var 0) (Syn.shift (pairT i m)))) := by
  refine .allI (.impI ?_)
  rw [shift_pair]
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := Common.pos_shift hm
  exact dig_lt hm'.wk

/-- The state `v_i` as a base-`m` number. -/
abbrev code (i m : PTm n) : PTm n := Cd rS dS m (pairT i m)

/-- A place value is a power of `m`. -/
theorem place (k i m : PTm n) : Γ ⊢[PRAAx] Pl rS k (pairT i m) ≐ pw m k := by
  refine prod_const_of rS k m (pairT i m) (.allI (.impI ?_))
  rw [shift_pair]
  exact r_at _ _ _

theorem code_bound {i m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] lt (code i m) (pw m m) :=
  lt_congr (.eqRefl _) (place m i m) (code_lt rS dS (pairT i m) m (dig_all hm m))

/-- Equal codes have equal digits. -/
theorem digit_eq {a b m k : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hc : Γ ⊢[PRAAx] code a m ≐ code b m) (hk : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] rem (bell (a + k)) m ≐ rem (bell (b + k)) m := by
  have em := eq_add_of_le hk
  have da := decode (r := rS) (d := dS) (x := pairT a m) (i := k) (t := monus m (succ k))
    (dig_all hm _)
  have db := decode (r := rS) (d := dS) (x := pairT b m) (i := k) (t := monus m (succ k))
    (dig_all hm _)
  have ca : Γ ⊢[PRAAx] Cd rS dS (succ k + monus m (succ k)) (pairT a m) ≐
      Cd rS dS (succ k + monus m (succ k)) (pairT b m) :=
    (congrAp2 _ em.eqSymm (.eqRefl _)).eqTrans (hc.eqTrans (congrAp2 _ em (.eqRefl _)))
  have pl : Γ ⊢[PRAAx] Pl rS k (pairT a m) ≐ Pl rS k (pairT b m) :=
    (place k a m).eqTrans (place k b m).eqSymm
  have rr : Γ ⊢[PRAAx] inst2 rS k (pairT a m) ≐ inst2 rS k (pairT b m) :=
    (r_at k a m).eqTrans (r_at k b m).eqSymm
  have e : Γ ⊢[PRAAx] inst2 dS k (pairT a m) ≐ inst2 dS k (pairT b m) :=
    da.eqSymm.eqTrans ((congrAp2 remF (congrAp2 quoF ca pl) rr).eqTrans db)
  exact (d_at k a m).eqSymm.eqTrans (e.eqTrans (d_at k b m))

theorem shift_code (i m : PTm n) : Syn.shift (code i m) = code (Syn.shift i) (Syn.shift m) := by
  simp [Syn.shift]

/-- Equal codes give `v_a = v_b`. -/
theorem collision_window {a b m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hc : Γ ⊢[PRAAx] code a m ≐ code b m) : Γ ⊢[PRAAx] W a b m ≐ one := by
  refine all_intro wB (.allI (.impI ?_))
  rw [shift_wpar]
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := Common.pos_shift hm
  have hc' : (Γ.map Fm.shift) ⊢[PRAAx]
      code (Syn.shift a) (Syn.shift m) ≐ code (Syn.shift b) (Syn.shift m) := by
    have h := hc.shift
    simp only [Fm.shift, Fm.subst_eq] at h
    rw [← shift_code, ← shift_code]
    exact h
  exact ne_of_one (w_intro (digit_eq hm'.wk hc'.wk Prf.hyp0))

/-! ## The collision -/

/-- The code as a body in `0 = i`, `1 = m`. -/
abbrev stB : PTm 2 := Cd rS dS (var 1) (pairT (var 0) (var 1))

theorem st_at (i m : PTm n) : inst2 stB i m = code i m := by simp [inst2]

/-- The code as a primitive recursive symbol. -/
abbrev fS : PR 2 := symbol stB

theorem f_at (i m : PTm n) : Γ ⊢[PRAAx] ap2 fS i m ≐ code i m := by
  have h := symbol_inst2 (Γ := Γ) stB i m
  rw [st_at] at h
  exact h

theorem f_range {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (d : PTm n) :
    Γ ⊢[PRAAx] rangeBelow fS d (pw m m) m := by
  refine .allI (.impI ?_)
  rw [shift_pw]
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := Common.pos_shift hm
  exact lt_congr (f_at _ _).eqSymm (.eqRefl _) (code_bound hm'.wk)

/-- The first colliding pair of indices `a < b ≤ m^m`. -/
abbrev ia (m : PTm n) : PTm n := first fS (pw m m) m
abbrev ib (m : PTm n) : PTm n := second fS (pw m m) m

/-- The period `T = b − a`. -/
abbrev Tm (m : PTm n) : PTm n := monus (ib m) (ia m)

theorem coll {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] lt (ia m) (ib m) ⋏
      (lt (ib m) (succ (pw m m)) ⋏ (ap2 fS (ia m) m ≐ ap2 fS (ib m) m)) :=
  collision fS (le_refl (succ (pw m m))) (f_range hm (succ (pw m m)))

/-! ## The period -/

/-- `v_T = v_0`. -/
theorem period_test {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Test (Tm m) m ≐ one := by
  have c := coll hm
  have hc : Γ ⊢[PRAAx] code (ia m) m ≐ code (ib m) m :=
    (f_at _ _).eqSymm.eqTrans ((Prf.andE₂ (Prf.andE₂ c)).eqTrans (f_at _ _))
  have eb : Γ ⊢[PRAAx] ib m ≐ ia m + Tm m := eq_add_of_le (le_of_lt (Prf.andE₁ c))
  exact window_back hm ((congrW (.eqRefl _) eb).eqSymm.eqTrans (collision_window hm hc))

/-- `1 ≤ T`. -/
theorem period_pos {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Tm m ≐ succ (pred (Tm m)) := by
  have c := Prf.andE₁ (coll hm)
  refine .orE (zero_or_succ (Tm m)) ?_ Prf.hyp0
  have e := eq_add_of_le (le_of_lt c)
  have hle : ((Tm m ≐ zero) :: Γ) ⊢[PRAAx] le (ib m) (ia m) :=
    le_of_eq_add (d := zero) ((e.wk.eqTrans
      ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))).eqSymm.eqTrans (add_zero _).eqSymm)
  exact not_succ_le_self _ _ (le_trans c.wk hle)

/-- `T ≤ m^m`. -/
theorem period_le {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (Tm m) (pw m m) := by
  have c := coll hm
  have h1 : Γ ⊢[PRAAx] le (ib m) (pw m m) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ c))
  have e := eq_add_of_le (le_of_lt (Prf.andE₁ c))
  exact le_trans (le_of_eq_add (d := ia m) (e.eqTrans (add_comm _ _))) h1

/-- `thm:all-moduli-period`: `B_{T+N} ≡ B_N (mod m)` for every `N`, with `1 ≤ T ≤ m^m`. -/
theorem bell_period_mod {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (Tm m + N)) m ≐ rem (bell N) m :=
  period_of_window hm (period_test hm) N

/-- `thm:all-moduli-period`, the uniform period: `B_{(m^m)!+N} ≡ B_N (mod m)`. -/
theorem bell_uniform_period {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (fact (pw m m) + N)) m ≐ rem (bell N) m := by
  have hp := period_pos hm
  have hd : Γ ⊢[PRAAx] dvd (succ (pred (Tm m))) (fact (pw m m)) :=
    dvd_fact (le_congr hp (.eqRefl _) (period_le hm))
  have w := eq_of_dvd hd
  have e : Γ ⊢[PRAAx] fact (pw m m) + N ≐
      quo (fact (pw m m)) (succ (pred (Tm m))) * Tm m + N := by
    ipra_lc natEq w - 𝔞 (quo (fact (pw m m)) (succ (pred (Tm m)))) * natEq hp
  exact (cong_of_eq (congrBell e)).eqTrans (window_mul hm (period_test hm) _ N)

/-- The uniform period, closed over `m − 1` and `N`. -/
theorem bell_uniform_period_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (rem (bell (fact (pw (succ (var 0)) (succ (var 0))) + var 1)) (succ (var 0)) ≐
        rem (bell (var 1)) (succ (var 0))) :=
  closeUniv 2 (bell_uniform_period (congrSucc (pred_succ _).eqSymm) _)

end LeanProofs.IPRA.Combinatorics.BellPeriodExists
