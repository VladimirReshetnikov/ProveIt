import IPRADerivations.Foundations.FiniteSetProducts
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.Header

/-!
# The exponential `[m]^[n] = [m^n]` as a universal object (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "The category of finite sets has
exponentials in iPRA", theorem "Finite exponentials": for all `n, m` the exponential `[m]^[n]`
exists in the table category and is `[m^n]`; "evaluation `ev : [m^n] × [n] → [m]` extracts the
`j`-th base-`m` digit", and for `h : [z] × [n] → [m]` the transpose sends `k` to the code of the
row `j ↦ h(k, j)`; "`ev ∘ (ĥ × 1) = h`" and "if `u` satisfies the same equation, then every
digit of `u(k)` agrees with the corresponding digit of `ĥ(k)`".

`Foundations/FiniteSetExponential` has the two entrywise inverse laws. Here they are stated in
the presentation `finSet` of `Foundations/FiniteSetCategory`, with the product `[a] × [b] = [ab]`
of `Foundations/FiniteSetProducts` (`(i, j) ↦ i b + j`), as equalities of codes of arrows:

* `evc n m`: the code of `ev : [m^n · n] → [m]`, `x ↦ ev(⌊x / n⌋, x mod n)` (`evc_hom`);
* `curryc z n m h`: the code of the transpose `[z] → [m^n]` of `h : [z n] → [m]`; its `i`-th
  entry is the code of the row `j ↦ ev(h, i n + j)` (`curry_hom`, `curry_ev_row`, `app_curry`);
* `xid z n e u`: the arrow `u × 1_n = ⟨u ∘ π₁, π₂⟩ : [z n] → [e n]` (`xid_hom`, `xid_ev`);
* `exp_beta`: `ev ∘ (curry h × 1) = h` for every arrow `h : [z n] → [m]`;
* `exp_eta`: `curry (ev ∘ (u × 1)) = u` for every arrow `u : [z] → [m^n]`;
* `exp_unique`: an arrow `u : [z] → [m^n]` with `ev ∘ (u × 1) = h` is `curry h`.

So `curry h` is the unique arrow whose transpose is `h`. The objects are the `[n]` with `n ≥ 1`
(the presentation `finSet`), hence the positivity hypotheses.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteSetClosed

open_ipra
open LeanProofs.IPRA.Probability.ProductPower (dg)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (pos_mul')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Foundations.FiniteSetExponential
open LeanProofs.IPRA.Foundations.FiniteSetCategory
open LeanProofs.IPRA.Foundations.FiniteSetProducts
open LeanProofs.IPRA.Foundations.PresentedCategory

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Congruence and shifting -/

/-- The digit respects equality of its index and of its code. -/
theorem dg_congr {m y y' c c' : PTm k} (hy : Γ ⊢[PRAAx] y ≐ y') (hc : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] dg m y c ≐ dg m y' c' :=
  congrAp2 remF (congrAp2 quoF hc (congrPw (.eqRefl _) hy)) (.eqRefl _)

theorem shift_pw'' (a b : PTm k) : Syn.shift (pw a b) = pw (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem shift_dg (m y c : PTm k) :
    Syn.shift (dg m y c) = dg (Syn.shift m) (Syn.shift y) (Syn.shift c) := by
  simp [Syn.shift]

theorem shift_lt'' {a b : PTm k} (h : Γ ⊢[PRAAx] lt a b) :
    Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_lt h

/-! ## The tables -/

/-- The evaluation table `x ↦ ev(⌊x / n⌋, x mod n)`; variables `0 = x`, `1 = ⟨n, m⟩`. -/
def evcT : PTm 2 :=
  dg (sndT (var 1)) (rem (var 0) (fstT (var 1))) (quo (var 0) (fstT (var 1)))

/-- The code of `ev : [m^n · n] → [m]`. -/
abbrev evc (n m : PTm k) : PTm k := code evcT (pw m n * n) m (pairT n m)

theorem evcT_at (x n m : PTm k) :
    Γ ⊢[PRAAx] inst2 evcT x (pairT n m) ≐ dg m (rem x n) (quo x n) := by
  have e₁ : inst2 evcT x (pairT n m) =
      Syn.subst ![x, fstT (pairT n m), sndT (pairT n m)]
        (dg (var 2 : PTm 3) (rem (var 0) (var 1)) (quo (var 0) (var 1))) := by
    show Syn.subst ![x, pairT n m] evcT = _
    simp [evcT]
  have e₂ : dg m (rem x n) (quo x n) =
      Syn.subst ![x, n, m] (dg (var 2 : PTm 3) (rem (var 0) (var 1)) (quo (var 0) (var 1))) := by
    simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact snd_pair _ _

/-- The row entry `ev(h, i n + j)`; variables `0 = j`, `1 = ⟨i, ⟨n, ⟨m, h⟩⟩⟩`. -/
def ciT : PTm 2 :=
  dg (fstT (sndT (sndT (var 1)))) (fstT (var 1) * fstT (sndT (var 1)) + var 0)
    (sndT (sndT (sndT (var 1))))

theorem ciT_at (j i n m h : PTm k) :
    Γ ⊢[PRAAx] inst2 ciT j (pairT i (pairT n (pairT m h))) ≐ dg m (i * n + j) h := by
  have e₁ : inst2 ciT j (pairT i (pairT n (pairT m h))) =
      Syn.subst ![j, fstT (pairT i (pairT n (pairT m h))),
          fstT (sndT (pairT i (pairT n (pairT m h)))),
          fstT (sndT (sndT (pairT i (pairT n (pairT m h))))),
          sndT (sndT (sndT (pairT i (pairT n (pairT m h)))))]
        (dg (var 3 : PTm 5) (var 1 * var 2 + var 0) (var 4)) := by
    show Syn.subst ![j, pairT i (pairT n (pairT m h))] ciT = _
    simp [ciT]
  have e₂ : dg m (i * n + j) h =
      Syn.subst ![j, i, n, m, h] (dg (var 3 : PTm 5) (var 1 * var 2 + var 0) (var 4)) := by
    simp
  rw [e₁, e₂]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT i (pairT n (pairT m h))) ≐ pairT n (pairT m h) :=
    snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT (pairT i (pairT n (pairT m h)))) ≐ pairT m h :=
    (congrSnd s₁).eqTrans (snd_pair _ _)
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrFst s₂).eqTrans (fst_pair _ _)
    · exact (congrSnd s₂).eqTrans (snd_pair _ _)

/-- The transposed entry: the code of the row `j ↦ ev(h, i n + j)`; variables `0 = i`,
`1 = ⟨n, ⟨m, h⟩⟩`. -/
def cuT : PTm 2 :=
  code ciT (fstT (var 1)) (fstT (sndT (var 1))) (pairT (var 0) (var 1))

/-- The code of the transpose `[z] → [m^n]` of `h : [z n] → [m]`. -/
abbrev curryc (z n m h : PTm k) : PTm k := code cuT z (pw m n) (pairT n (pairT m h))

theorem cuT_at (i n m h : PTm k) :
    Γ ⊢[PRAAx] inst2 cuT i (pairT n (pairT m h)) ≐
      code ciT n m (pairT i (pairT n (pairT m h))) := by
  have e : inst2 cuT i (pairT n (pairT m h)) =
      code ciT (fstT (pairT n (pairT m h))) (fstT (sndT (pairT n (pairT m h))))
        (pairT i (pairT n (pairT m h))) := by
    show Syn.subst ![i, pairT n (pairT m h)] cuT = _
    simp [cuT]
  rw [e]
  exact congrAp2 _ (fst_pair _ _)
    (congrPairT ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))

/-- `u × 1_n = ⟨u ∘ π₁, π₂⟩ : [z n] → [e n]` for `u : [z] → [e]`. -/
abbrev xid (z n e u : PTm k) : PTm k :=
  pairc (z * n) e n (cmpc (z * n) z e u (p1c z n)) (p2c z n)

theorem shift_evc (n m : PTm k) : Syn.shift (evc n m) = evc (Syn.shift n) (Syn.shift m) := by
  simp [Syn.shift]

theorem shift_curryc (z n m h : PTm k) :
    Syn.shift (curryc z n m h) =
      curryc (Syn.shift z) (Syn.shift n) (Syn.shift m) (Syn.shift h) := by
  simp [Syn.shift]

theorem shift_xid (z n e u : PTm k) :
    Syn.shift (xid z n e u) = xid (Syn.shift z) (Syn.shift n) (Syn.shift e) (Syn.shift u) := by
  simp [Syn.shift]

/-- The transpose respects equality of the transposed arrow. -/
theorem curry_congr {z n m h h' : PTm k} (e : Γ ⊢[PRAAx] h ≐ h') :
    Γ ⊢[PRAAx] curryc z n m h ≐ curryc z n m h' :=
  congrAp2 _ (.eqRefl _)
    (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) e)))

/-! ## Entrywise evaluation -/

/-- `ev(ev, y) = ev(⌊y / n⌋, y mod n)` for `y < m^n · n`. -/
theorem evc_ev {n m y : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hy : Γ ⊢[PRAAx] lt y (pw m n * n)) :
    Γ ⊢[PRAAx] dg m y (evc n m) ≐ dg m (rem y n) (quo y n) :=
  (ev_curry evcT hm hy (pairT n m)).eqTrans
    ((congrAp2 remF (evcT_at y n m) (.eqRefl _)).eqTrans (rem_of_lt hm (dg_lt hm _ _)))

/-- The `i`-th entry of the transpose is the code of the `i`-th row. -/
theorem curry_ev_row {z n m h i : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hi : Γ ⊢[PRAAx] lt i z) :
    Γ ⊢[PRAAx] dg (pw m n) i (curryc z n m h) ≐ code ciT n m (pairT i (pairT n (pairT m h))) :=
  (ev_curry cuT (pw_pos' hm n) hi (pairT n (pairT m h))).eqTrans
    ((congrAp2 remF (cuT_at i n m h) (.eqRefl _)).eqTrans
      (rem_of_lt (pw_pos' hm n) (code_lt ciT hm n _)))

/-- The `j`-th digit of the `i`-th row code is `ev(h, i n + j)`. -/
theorem row_ev {n m h i j : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hj : Γ ⊢[PRAAx] lt j n) :
    Γ ⊢[PRAAx] dg m j (code ciT n m (pairT i (pairT n (pairT m h)))) ≐ dg m (i * n + j) h :=
  (ev_curry ciT hm hj _).eqTrans
    ((congrAp2 remF (ciT_at j i n m h) (.eqRefl _)).eqTrans (rem_of_lt hm (dg_lt hm _ _)))

/-- Application of the transpose: `ev(ev(curry h, i), j) = ev(h, i n + j)`. -/
theorem app_curry {z n m h i j : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hi : Γ ⊢[PRAAx] lt i z) (hj : Γ ⊢[PRAAx] lt j n) :
    Γ ⊢[PRAAx] dg m j (dg (pw m n) i (curryc z n m h)) ≐ dg m (i * n + j) h :=
  (dg_congr (.eqRefl _) (curry_ev_row hm hi)).eqTrans (row_ev hm hj)

/-- `ev(u × 1, x) = ev(u, ⌊x / n⌋) n + (x mod n)` for `x < z n`. -/
theorem xid_ev {z n e u x : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hx : Γ ⊢[PRAAx] lt x (z * n)) :
    Γ ⊢[PRAAx] dg (e * n) x (xid z n e u) ≐ dg e (quo x n) u * n + rem x n :=
  (pair_ev he hn hx).eqTrans
    (congrAdd (congrMul ((ev_comp he hx).eqTrans (dg_idx (p1_ev hz hn hx))) (.eqRefl _))
      (p2_ev hn hx))

/-- `ev(ev, ev(u × 1, x)) = ev(ev(u, ⌊x / n⌋), x mod n)` for `x < z n`. -/
theorem ev_xid {z n m u x : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hx : Γ ⊢[PRAAx] lt x (z * n)) :
    Γ ⊢[PRAAx] dg m (dg (pw m n * n) x (xid z n (pw m n) u)) (evc n m) ≐
      dg m (rem x n) (dg (pw m n) (quo x n) u) := by
  have he := pw_pos' hm n
  have hr := snd_lt hn x
  have hY := pair_lt (dg_lt he (quo x n) u) hr
  exact (dg_idx (xid_ev hz hn he hx)).eqTrans
    ((evc_ev hm hY).eqTrans (dg_congr (pair_snd hn hr) (pair_fst hn hr)))

theorem beta_pt {z n m h x : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hx : Γ ⊢[PRAAx] lt x (z * n)) :
    Γ ⊢[PRAAx] inst2 cmT x (pairT (pw m n * n) (pairT m (pairT (evc n m)
        (xid z n (pw m n) (curryc z n m h))))) ≐
      inst2 evT x (pairT m h) :=
  (cmT_at x (pw m n * n) m (evc n m) _).eqTrans
    ((ev_xid hz hn hm hx).eqTrans
      ((app_curry hm (fst_lt hn hx) (snd_lt hn x)).eqTrans
        ((dg_idx (pair_eta hn x).eqSymm).eqTrans (evT_at x m h).eqSymm)))

theorem eta_in {z n m u i j : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hi : Γ ⊢[PRAAx] lt i z) (hj : Γ ⊢[PRAAx] lt j n) :
    Γ ⊢[PRAAx] inst2 ciT j (pairT i (pairT n (pairT m
        (cmpc (z * n) (pw m n * n) m (evc n m) (xid z n (pw m n) u))))) ≐
      inst2 evT j (pairT m (dg (pw m n) i u)) := by
  have hx := pair_lt hi hj
  exact (ciT_at j i n m _).eqTrans
    ((ev_comp hm hx).eqTrans
      ((ev_xid hz hn hm hx).eqTrans
        ((dg_congr (pair_snd hn hj) (dg_idx (pair_fst hn hj))).eqTrans (evT_at j m _).eqSymm)))

/-- The `i`-th row of `ev ∘ (u × 1)` has code `ev(u, i)`. -/
theorem eta_row {z n m u i : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hi : Γ ⊢[PRAAx] lt i z) :
    Γ ⊢[PRAAx] code ciT n m (pairT i (pairT n (pairT m
        (cmpc (z * n) (pw m n * n) m (evc n m) (xid z n (pw m n) u))))) ≐
      dg (pw m n) i u := by
  refine .eqTrans (code_congr ciT evT (q' := pairT m (dg (pw m n) i u)) (.allI (.impI ?_)))
    (curry_ev hm (dg_lt (pw_pos' hm n) i u))
  simp only [shift_pairT, shift_mul', shift_pw'', shift_evc, shift_xid, shift_cmpc, shift_dg]
  have hz' := hz.shift
  rw [shift_pos] at hz'
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hm' := hm.shift
  rw [shift_pos] at hm'
  exact congrAp2 remF (eta_in hz'.wk hn'.wk hm'.wk (shift_lt'' hi).wk Prf.hyp0) (.eqRefl _)

theorem eta_pt {z n m u i : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hi : Γ ⊢[PRAAx] lt i z) :
    Γ ⊢[PRAAx] inst2 cuT i (pairT n (pairT m
        (cmpc (z * n) (pw m n * n) m (evc n m) (xid z n (pw m n) u)))) ≐
      inst2 evT i (pairT (pw m n) u) :=
  (cuT_at i n m _).eqTrans ((eta_row hz hn hm hi).eqTrans (evT_at i (pw m n) u).eqSymm)

/-! ## The arrows and the universal property -/

/-- `ev : [m^n · n] → [m]`. -/
theorem evc_hom {n m : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] finSet.hom (pw m n * n) m (evc n m) := by
  rw [fs_hom]
  exact .andI (pos_mul' (pw_pos' hm n) hn) (.andI hm (code_lt evcT hm _ _))

/-- `curry h : [z] → [m^n]`. -/
theorem curry_hom {z n m h : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] finSet.hom z (pw m n) (curryc z n m h) := by
  rw [fs_hom]
  exact .andI hz (.andI (pw_pos' hm n) (code_lt cuT (pw_pos' hm n) z _))

/-- `u × 1_n : [z n] → [e n]`. -/
theorem xid_hom {z n e u : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) :
    Γ ⊢[PRAAx] finSet.hom (z * n) (e * n) (xid z n e u) := by
  rw [fs_hom]
  exact .andI (pos_mul' hz hn) (.andI (pos_mul' he hn) (code_lt prT (pos_mul' he hn) (z * n) _))

/-- `ev ∘ (curry h × 1) = h` for `h : [z n] → [m]`. -/
theorem exp_beta {z n m h : PTm k} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hh : Γ ⊢[PRAAx] finSet.hom (z * n) m h) :
    Γ ⊢[PRAAx] cmpc (z * n) (pw m n * n) m (evc n m) (xid z n (pw m n) (curryc z n m h)) ≐
      h := by
  rw [fs_hom] at hh
  have hm := Prf.andE₁ (Prf.andE₂ hh)
  refine .eqTrans (code_congr cmT evT (q' := pairT m h) (.allI (.impI ?_)))
    (curry_ev hm (Prf.andE₂ (Prf.andE₂ hh)))
  simp only [shift_pairT, shift_mul', shift_pw'', shift_evc, shift_xid, shift_curryc]
  have hz' := hz.shift
  rw [shift_pos] at hz'
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hm' := hm.shift
  rw [shift_pos] at hm'
  exact congrAp2 remF (beta_pt hz'.wk hn'.wk hm'.wk Prf.hyp0) (.eqRefl _)

/-- `curry (ev ∘ (u × 1)) = u` for `u : [z] → [m^n]`. -/
theorem exp_eta {z n m u : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hu : Γ ⊢[PRAAx] finSet.hom z (pw m n) u) :
    Γ ⊢[PRAAx] curryc z n m (cmpc (z * n) (pw m n * n) m (evc n m) (xid z n (pw m n) u)) ≐
      u := by
  rw [fs_hom] at hu
  have hz := Prf.andE₁ hu
  refine .eqTrans (code_congr cuT evT (q' := pairT (pw m n) u) (.allI (.impI ?_)))
    (curry_ev (pw_pos' hm n) (Prf.andE₂ (Prf.andE₂ hu)))
  simp only [shift_pairT, shift_mul', shift_pw'', shift_evc, shift_xid, shift_cmpc]
  have hz' := hz.shift
  rw [shift_pos] at hz'
  have hn' := hn.shift
  rw [shift_pos] at hn'
  have hm' := hm.shift
  rw [shift_pos] at hm'
  exact congrAp2 remF (eta_pt hz'.wk hn'.wk hm'.wk Prf.hyp0) (.eqRefl _)

/-- Uniqueness of the transpose: an arrow `u : [z] → [m^n]` with `ev ∘ (u × 1) = h` is
`curry h`. -/
theorem exp_unique {z n m u h : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hu : Γ ⊢[PRAAx] finSet.hom z (pw m n) u)
    (e : Γ ⊢[PRAAx] cmpc (z * n) (pw m n * n) m (evc n m) (xid z n (pw m n) u) ≐ h) :
    Γ ⊢[PRAAx] u ≐ curryc z n m h :=
  (exp_eta hn hm hu).eqSymm.eqTrans (curry_congr e)

end LeanProofs.IPRA.Foundations.FiniteSetClosed
