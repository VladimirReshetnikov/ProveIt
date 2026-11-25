import IPRADerivations.Combinatorics.BellWindowPeriod
import IPRADerivations.Core.CertificateTactics

/-!
# The backward recurrence for Bell windows modulo `m` (`bell_numbers_ipra`, `thm:all-moduli-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:all-moduli-period`: the transition of the state vector `v_n = (B_n, …, B_{n+m−1}) mod m`
"is a bijection: from the new state, recover the discarded entry by adding
`∑_{j=1}^{m−1} c_j B_{n+j}` to its last entry. ... If `v_a = v_b` with `0 ≤ a < b ≤ m^m`,
apply the explicit inverse transition `a` times to get `v_0 = v_{b−a}`."

With the bit `W a b m` of the `m` congruences `B_{a+i} ≡ B_{b+i} (mod m)`, `i < m` (`v_a = v_b`):

* `back_zero`: `v_{a+1} = v_{b+1}` gives `B_a ≡ B_b`, by `recurrence_split` at `a` and at `b`
  (the recurrence read backwards);
* `back_step`: `v_{a+1} = v_{b+1}` gives `v_a = v_b`;
* `back_all`: `v_a = v_{a+T}` gives `v_0 = v_T`, by `a` backward steps (quantifier-free
  induction on the number of steps);
* `window_back`: hence `Test T m`, the matching window of `Combinatorics/BellWindowPeriod`,
  and `T` is a period at every index.

Not derived here: the collision `v_a = v_b` itself (pigeonhole on the state codes).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellWindowBackward

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (cong_add cong_mul cong_of_eq cong_sum
  shift_pair monus_of_lt)
open LeanProofs.IPRA.Combinatorics.BellPeriodNp (bellB shift_zero)
open LeanProofs.IPRA.Combinatorics.BellModularRecurrence (recurrence_split MidB)
open LeanProofs.IPRA.Combinatorics.BellLeastPeriod (eB e_intro Test ne_of_one)
open LeanProofs.IPRA.Combinatorics.BellWindowPeriod (sh_at)
open LeanProofs.IPRA.Combinatorics.LinearFactorTable (cyc actB pair_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_elim all_intro)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Two windows -/

/-- The parameter `⟨⟨a, b⟩, m⟩`. -/
abbrev wpar (a b m : PTm n) : PTm n := pairT (pairT a b) m

/-- The bit `[B_{a+i} ≡ B_{b+i} (mod m)]`, over `0 = i`, `1 = ⟨⟨a, b⟩, m⟩`. -/
abbrev wB : PTm 2 :=
  eqb (rem (bell (fstT (fstT (var 1)) + var 0)) (sndT (var 1)))
    (rem (bell (sndT (fstT (var 1)) + var 0)) (sndT (var 1)))

theorem w_at (i a b m : PTm n) :
    Γ ⊢[PRAAx] inst2 wB i (wpar a b m) ≐ eqb (rem (bell (a + i)) m) (rem (bell (b + i)) m) := by
  have h : inst2 wB i (wpar a b m) =
      eqb (rem (bell (fstT (fstT (wpar a b m)) + i)) (sndT (wpar a b m)))
        (rem (bell (sndT (fstT (wpar a b m)) + i)) (sndT (wpar a b m))) := by simp [inst2]
  rw [h]
  have ha : Γ ⊢[PRAAx] fstT (fstT (wpar a b m)) ≐ a :=
    (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have hb : Γ ⊢[PRAAx] sndT (fstT (wpar a b m)) ≐ b :=
    (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrEqb (congrAp2 remF (congrBell (congrAdd ha (.eqRefl _))) (snd_pair _ _))
    (congrAp2 remF (congrBell (congrAdd hb (.eqRefl _))) (snd_pair _ _))

theorem w_elim {i a b m : PTm n} (h : Γ ⊢[PRAAx] neg (inst2 wB i (wpar a b m) ≐ zero)) :
    Γ ⊢[PRAAx] rem (bell (a + i)) m ≐ rem (bell (b + i)) m :=
  eq_of_eqb_ne (.impI (.impE h.wk ((w_at i a b m).eqTrans Prf.hyp0)))

theorem w_intro {i a b m : PTm n} (h : Γ ⊢[PRAAx] rem (bell (a + i)) m ≐ rem (bell (b + i)) m) :
    Γ ⊢[PRAAx] inst2 wB i (wpar a b m) ≐ one :=
  (w_at i a b m).eqTrans (eqb_of_eq h)

/-- `v_a = v_b`: the `m` congruences `B_{a+i} ≡ B_{b+i} (mod m)`, `i < m`, as one bit. -/
abbrev W (a b m : PTm n) : PTm n := allB wB m (wpar a b m)

theorem congrW {a a' b b' m : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] W a b m ≐ W a' b' m :=
  congrAp2 _ (.eqRefl _) (pair_congr (pair_congr ha hb) (.eqRefl _))

theorem shift_wpar (a b m : PTm n) :
    Syn.shift (wpar a b m) = wpar (Syn.shift a) (Syn.shift b) (Syn.shift m) := by
  simp [Syn.shift]

/-! ## One backward step -/

theorem mid_pt2 {a b m K : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hW : Γ ⊢[PRAAx] W (succ a) (succ b) m ≐ one) (hK : Γ ⊢[PRAAx] lt K (pred m)) :
    Γ ⊢[PRAAx]
      rem (inst2 (shiftBody (actB bellB)) K (LinearFactorTable.par m a zero)) m ≐
        rem (inst2 (shiftBody (actB bellB)) K (LinearFactorTable.par m b zero)) m := by
  have hlt : Γ ⊢[PRAAx] lt K m :=
    le_trans hK (le_congr (.eqRefl _) hm.eqSymm (le_succ_self (pred m)))
  have h0 := w_elim (all_elim wB hW hlt)
  have h : Γ ⊢[PRAAx] rem (bell (a + succ K)) m ≐ rem (bell (b + succ K)) m :=
    (cong_of_eq (congrBell (a := a + succ K) (b := succ a + K)
      (by ipra_ring))).eqTrans
      (h0.eqTrans (cong_of_eq (congrBell (a := succ b + K) (b := b + succ K)
        (by ipra_ring))))
  exact (cong_of_eq (sh_at K m a)).eqTrans
    ((cong_mul (cyc m (succ K)) hm h).eqTrans (cong_of_eq (sh_at K m b)).eqSymm)

/-- The discarded entry is recovered: `v_{a+1} = v_{b+1}` gives `B_a ≡ B_b`. -/
theorem back_zero {a b m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hW : Γ ⊢[PRAAx] W (succ a) (succ b) m ≐ one) :
    Γ ⊢[PRAAx] rem (bell a) m ≐ rem (bell b) m := by
  have hpm : Γ ⊢[PRAAx] lt (pred m) m := le_congr (.eqRefl _) hm.eqSymm (le_refl _)
  have h0 := w_elim (all_elim wB hW hpm)
  have top : Γ ⊢[PRAAx] rem (bell (a + m)) m ≐ rem (bell (b + m)) m := by
    have ea : Γ ⊢[PRAAx] a + m ≐ succ a + pred m := by
      have x := natEq hm
      apply deriveNat; ipra_simps
      linear_combination x
    have eb : Γ ⊢[PRAAx] succ b + pred m ≐ b + m := by
      have x := natEq hm
      apply deriveNat; ipra_simps
      linear_combination -x
    exact (cong_of_eq (congrBell ea)).eqTrans (h0.eqTrans (cong_of_eq (congrBell eb)))
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
    simpa [Fm.shift, Syn.shift] using hm.shift
  have hW' : (Γ.map Fm.shift) ⊢[PRAAx]
      W (succ (Syn.shift a)) (succ (Syn.shift b)) (Syn.shift m) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hW.shift
  have e : Syn.shift (pred m) = pred (Syn.shift m) := by simp [Syn.shift]
  have mid : Γ ⊢[PRAAx] rem (MidB m a) m ≐ rem (MidB m b) m :=
    cong_sum (shiftBody (actB bellB)) (shiftBody (actB bellB)) hm (.allI (.impI (by
      simp only [shift_pair, shift_zero]
      exact mid_pt2 hm'.wk hW'.wk (by rw [← e]; exact Prf.hyp0))))
  exact (recurrence_split hm a).eqSymm.eqTrans
    ((cong_add hm top mid).eqTrans (recurrence_split hm b))

theorem back_pt {a b m i : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hW : Γ ⊢[PRAAx] W (succ a) (succ b) m ≐ one) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] neg (inst2 wB i (wpar a b m) ≐ zero) := by
  refine ne_of_one (w_intro (.orE (zero_or_succ i) ?_ ?_))
  · exact (cong_of_eq (congrBell ((congrAdd (.eqRefl a) Prf.hyp0).eqTrans (add_zero a)))).eqTrans
      ((back_zero hm.wk hW.wk).eqTrans
        (cong_of_eq (congrBell ((congrAdd (.eqRefl b) Prf.hyp0).eqTrans (add_zero b)))).eqSymm)
  · have hs : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp0
    have hlt : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] lt (pred i) m :=
      le_congr hs (.eqRefl _) (le_trans (le_succ_self i) hi.wk)
    have h0 := w_elim (all_elim wB hW.wk hlt)
    have ea : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] a + i ≐ succ a + pred i := by
      have x := natEq hs
      apply deriveNat; ipra_simps
      linear_combination x
    have eb : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] succ b + pred i ≐ b + i := by
      have x := natEq hs
      apply deriveNat; ipra_simps
      linear_combination -x
    exact (cong_of_eq (congrBell ea)).eqTrans (h0.eqTrans (cong_of_eq (congrBell eb)))

/-- The inverse transition: `v_{a+1} = v_{b+1}` gives `v_a = v_b`. -/
theorem back_step {a b m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hW : Γ ⊢[PRAAx] W (succ a) (succ b) m ≐ one) : Γ ⊢[PRAAx] W a b m ≐ one := by
  refine all_intro wB (.allI (.impI ?_))
  rw [shift_wpar]
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
    simpa [Fm.shift, Syn.shift] using hm.shift
  have hW' : (Γ.map Fm.shift) ⊢[PRAAx]
      W (succ (Syn.shift a)) (succ (Syn.shift b)) (Syn.shift m) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hW.shift
  exact back_pt hm'.wk hW'.wk Prf.hyp0

/-! ## `a` backward steps -/

/-- The induction formula; variable `0` is the number of backward steps. -/
abbrev backF (a T m : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift a) ⟶
    (W (monus (Syn.shift a) (var 0)) (monus (Syn.shift a) (var 0) + Syn.shift T) (Syn.shift m) ≐ one)

theorem back_link {a T m k : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (ih : Γ ⊢[PRAAx] W (monus a k) (monus a k + T) m ≐ one) (hk : Γ ⊢[PRAAx] lt k a) :
    Γ ⊢[PRAAx] W (monus a (succ k)) (monus a (succ k) + T) m ≐ one := by
  have e := monus_of_lt hk
  have e2 : Γ ⊢[PRAAx] monus a k + T ≐ succ (monus a (succ k) + T) := by
    ipra_lc natEq e
  exact back_step hm ((congrW e e2).eqSymm.eqTrans ih)

/-- `v_a = v_{a+T}` gives `v_0 = v_T`. -/
theorem back_all {a T m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hW : Γ ⊢[PRAAx] W a (a + T) m ≐ one) : Γ ⊢[PRAAx] W zero T m ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (backF a T m) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · have b : (le zero a :: Γ) ⊢[PRAAx] W (monus a zero) (monus a zero + T) m ≐ one :=
        (congrW (monus_zero a) (congrAdd (monus_zero a) (.eqRefl T))).eqTrans hW.wk
      simpa using .impI b
    · have hm' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
        simpa [Fm.shift, Syn.shift] using hm.shift
      have st : (backF a T m :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift a) ⟶
          (W (monus (Syn.shift a) (succ (var 0)))
            (monus (Syn.shift a) (succ (var 0)) + Syn.shift T) (Syn.shift m) ≐ one) :=
        .impI (back_link hm'.wk.wk
          (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)) Prf.hyp0)
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE a hall
  have h3 : Γ ⊢[PRAAx] le a a ⟶ (W (monus a a) (monus a a + T) m ≐ one) := by
    simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2
  have z : Γ ⊢[PRAAx] monus a a + T ≐ T :=
    (congrAdd (monus_self a) (.eqRefl T)).eqTrans (zero_add T)
  exact (congrW (monus_self a) z).eqSymm.eqTrans (Prf.impE h3 (le_refl a))

/-! ## The matching window -/

theorem e_of_w {i T m : PTm n} (hW : Γ ⊢[PRAAx] W zero T m ≐ one) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] neg (inst2 eB i (pairT T m) ≐ zero) :=
  ne_of_one (e_intro ((w_elim (all_elim wB hW hi)).eqSymm.eqTrans
    (cong_of_eq (congrBell (zero_add i)))))

/-- `v_a = v_{a+T}` gives the matching window `Test T m` (`v_T = v_0`). -/
theorem window_back {a T m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hW : Γ ⊢[PRAAx] W a (a + T) m ≐ one) : Γ ⊢[PRAAx] Test T m ≐ one := by
  refine all_intro eB (.allI (.impI ?_))
  rw [shift_pair]
  have h0 := back_all hm hW
  have h0' : (Γ.map Fm.shift) ⊢[PRAAx] W zero (Syn.shift T) (Syn.shift m) ≐ one := by
    simpa [Fm.shift, Syn.shift] using h0.shift
  exact e_of_w h0'.wk Prf.hyp0

end LeanProofs.IPRA.Combinatorics.BellWindowBackward
