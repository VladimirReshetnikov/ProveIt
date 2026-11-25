import IPRADerivations.Probability.ProductPower
import IPRADerivations.Core.CertificateTactics

/-!
# Wald's identity on the finite product law

Packet: `probability/expected_value_ipra_2026-11-16`, Theorem `thm:wald`.

`X_j = X(dg_j t)` are the iid coordinates of the `N`-fold product law `P_N` of a finite law `w` over
`M ≥ 1` outcomes (`Probability/ProductPower`). A stopping time `T ≤ N` is given through its tail
indicators `[T > j]`, which may depend only on the first `j` coordinates, i.e. only on `t mod M^j`:
`[T > j](t) = g(j, t mod M^j)` for a body `g`. Then `∑_{j<T} X_j = ∑_{j<N} X_j [T > j]` and
`T = ∑_{j<N} [T > j]`, so with

  `Q_r(Y) = ∑_{t<M^r} P_r(t) ∑_{j<r} Y(dg_j t) g(j, t mod M^j)`,

Wald's identity `E[∑_{j<T} X_j] = μ E[T]` reads, cleared of `W = ∑ w` and `μ = (∑ w X)/W`,
`W Q_N(X) = (∑ w X) Q_N(1)` (`wald`). No property of `g` other than this dependence is used.

* `I_low`, `I_peel`: the inner sum over `j < r` does not see the top coordinate, and the new term at
  `j = r` is `Y(a) g(r, u)` for `t = a M^r + u`;
* `block_Q`, `Q_succ`: `Q_{r+1}(Y) = W Q_r(Y) + (∑ w Y) G_r` with `G_r = ∑_{u<M^r} P_r(u) g(r, u)`;
* `wald`: quantifier-free induction on `r`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Wald

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.BlockSum (qr_block)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Probability.ProductPower (dg dB_at dg_low dg_top rem_shift TB TB_at Pr pr_peel peel_sum lin3
  shift_inst2' one_bound)
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Bodies

variable (w Y G : PTm 2)

/-- `g(j, u) = G(u, ⟨j, x⟩)` read at `u = t mod M^j`, over `0 = j`, `1 = ⟨t, ⟨M, x⟩⟩`. -/
abbrev gdB : PTm 2 :=
  Syn.subst ![rem (fstT (var 1)) (pw (fstT (sndT (var 1))) (var 0)), pairT (var 0) (sndT (sndT (var 1)))] G

/-- `Y(dg_j t) g(j, t mod M^j)`, over `0 = j`, `1 = ⟨t, ⟨M, x⟩⟩`. -/
abbrev IB : PTm 2 := Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] Y * gdB G

/-- The inner sum `I_r(t) = ∑_{j<r} Y(dg_j t) g(j, t mod M^j)`. -/
abbrev Ir (r t M x : PTm n) : PTm n := ap2 (sumF (IB Y G)) r (pairT t (pairT M x))

theorem gdB_at (j t M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (gdB G) j (pairT t (pairT M x)) ≐ inst2 G (rem t (pw M j)) (pairT j x) := by
  have e : inst2 (gdB G) j (pairT t (pairT M x)) =
      inst2 G (rem (fstT (pairT t (pairT M x))) (pw (fstT (sndT (pairT t (pairT M x)))) j))
        (pairT j (sndT (sndT (pairT t (pairT M x))))) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]
  have hM : Γ ⊢[PRAAx] fstT (sndT (pairT t (pairT M x))) ≐ M := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT t (pairT M x))) ≐ x := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  exact congrInst2 G (congrAp2 remF (fst_pair _ _) (Combinatorics.BinomialTheorem.congrPw hM (.eqRefl _)))
    (congrPairT (.eqRefl _) hx)

theorem IB_at (j t M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (IB Y G) j (pairT t (pairT M x)) ≐ inst2 Y (dg M j t) x * inst2 G (rem t (pw M j)) (pairT j x) := by
  rw [inst2_mul']
  exact congrMul (dB_at Y _ _ _ _) (gdB_at G _ _ _ _)

/-- `t mod M^j` does not see a top coordinate above `j`: `(a M^r + u) mod M^j = u mod M^j` for `j ≤ r`. -/
theorem rem_low {M a u j r : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hj : Γ ⊢[PRAAx] le j r) :
    Γ ⊢[PRAAx] rem (a * pw M r + u) (pw M j) ≐ rem u (pw M j) := by
  have hMj := pw_pos' hM j
  have pr : Γ ⊢[PRAAx] pw M r ≐ pw M (monus r j) * pw M j :=
    (Combinatorics.BinomialTheorem.congrPw (.eqRefl _) ((eq_add_of_le hj).eqTrans (add_comm _ _))).eqTrans (pw_add _ _ _)
  have p := natEq pr
  refine .eqTrans ?_ (rem_shift (c := a * pw M (monus r j)) hMj)
  exact congrAp2 remF (by apply deriveNat; ipra_simps; linear_combination 𝔞 a * p) (.eqRefl _)

/-- The inner terms below `r` do not see the top coordinate. -/
theorem I_low {M a u r x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift r) ⟶
      (inst2 (IB Y G) (var 0) (Syn.shift (pairT (a * pw M r + u) (pairT M x))) ≐
        inst2 (IB Y G) (var 0) (Syn.shift (pairT u (pairT M x))))) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine .allI (.impI ?_)
  simp only [shift_pairT]
  rw [show Syn.shift (a * pw M r + u) = Syn.shift a * pw (Syn.shift M) (Syn.shift r) + Syn.shift u by simp [Syn.shift]]
  refine (IB_at Y G _ _ _ _).eqTrans (.eqTrans ?_ (IB_at Y G _ _ _ _).eqSymm)
  exact congrMul (congrInst2 Y (dg_low hM'.wk Prf.hyp0) (.eqRefl _))
    (congrInst2 G (rem_low hM'.wk (le_of_lt Prf.hyp0)) (.eqRefl _))

/-- `I_{r+1}(a M^r + u) = I_r(u) + Y(a) g(r, u)` for `a < M`, `u < M^r`. -/
theorem I_peel {M a u r x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M)
    (hu : Γ ⊢[PRAAx] lt u (pw M r)) :
    Γ ⊢[PRAAx] Ir Y G (succ r) (a * pw M r + u) M x ≐ Ir Y G r u M x + inst2 Y a x * inst2 G u (pairT r x) := by
  refine (sum_succ' _ _ _).eqTrans (congrAdd (sum_congr_bounded _ _ _ _ _ (I_low Y G hM)) ?_)
  refine (IB_at Y G _ _ _ _).eqTrans (congrMul (congrInst2 Y (dg_top hM ha hu) (.eqRefl _)) ?_)
  have r0 := Prf.andE₂ (qr_block (i := a) (j := u) (pw_pos' hM r) hu)
  exact congrInst2 G r0 (.eqRefl _)

end Bodies

section Totals

variable (w Y G : PTm 2)

/-- `P_r(t) I_r(t)`, over `0 = t`, `1 = ⟨r, ⟨M, x⟩⟩`. -/
abbrev QB : PTm 2 := TB w * ap2 (sumF (IB Y G)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))
/-- `P_r(t) g(r, t)`, over `0 = t`, `1 = ⟨r, ⟨M, x⟩⟩`. -/
abbrev GB : PTm 2 := TB w * Syn.subst ![var 0, pairT (fstT (var 1)) (sndT (sndT (var 1)))] G

/-- `Q_r(Y) = ∑_{t<M^r} P_r(t) I_r(t)`. -/
abbrev Qt (r M x : PTm n) : PTm n := ap2 (sumF (QB w Y G)) (pw M r) (pairT r (pairT M x))
/-- `G_r = ∑_{t<M^r} P_r(t) g(r, t)`. -/
abbrev Gt (r M x : PTm n) : PTm n := ap2 (sumF (GB w G)) (pw M r) (pairT r (pairT M x))

theorem QB_at (t r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (QB w Y G) t (pairT r (pairT M x)) ≐ Pr w r t M x * Ir Y G r t M x := by
  rw [inst2_mul']
  have e : inst2 (ap2 (sumF (IB Y G)) (fstT (var 1)) (pairT (var 0) (sndT (var 1))) : PTm 2) t (pairT r (pairT M x)) =
      ap2 (sumF (IB Y G)) (fstT (pairT r (pairT M x))) (pairT t (sndT (pairT r (pairT M x)))) := by simp [inst2]
  rw [e]
  exact congrMul (TB_at w _ _ _ _) (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _)))

theorem GB_at (t r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (GB w G) t (pairT r (pairT M x)) ≐ Pr w r t M x * inst2 G t (pairT r x) := by
  rw [inst2_mul']
  have e : inst2 (Syn.subst ![var 0, pairT (fstT (var 1)) (sndT (sndT (var 1)))] G) t (pairT r (pairT M x)) =
      inst2 G t (pairT (fstT (pairT r (pairT M x))) (sndT (sndT (pairT r (pairT M x))))) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]
  exact congrMul (TB_at w _ _ _ _) (congrInst2 G (.eqRefl _)
    (congrPairT (fst_pair _ _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))))

theorem inst2_zero2 (v p : PTm n) : inst2 (zero : PTm 2) v p = zero := by simp [inst2]

/-- One block of `Q_{r+1}(Y)`: `∑_{u<M^r} P_{r+1}(a M^r + u) I_{r+1}(a M^r + u) = w(a) Q_r + w(a) Y(a) G_r`. -/
theorem block_Q {a r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M) :
    Γ ⊢[PRAAx] inst2 (BlockSum.blkB (QB w Y G)) a (pairT (pw M r) (pairT (succ r) (pairT M x))) ≐
      inst2 w a x * Qt w Y G r M x + ((inst2 w a x * inst2 Y a x) * Gt w G r M x +
        zero * ap2 (sumF (zero : PTm 2)) (pw M r) (pairT r (pairT M x))) := by
  refine (BlockSum.blk_at _ _ _ _).eqTrans (lin3 (QB w Y G) (GB w G) (zero : PTm 2) (offB (QB w Y G)) (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have ha' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift M) := by
    have e := ha.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  simp only [shift_pairT, ProductPower.shift_mul'', shift_inst2', ProductPower.shift_zero']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hp, hs, inst2_zero2, inst2_offB]
  let C : List (Fm PTm (n + 1)) := lt (var 0) (pw (Syn.shift M) (Syn.shift r)) :: Γ.map Fm.shift
  have hu : C ⊢[PRAAx] lt (var 0) (pw (Syn.shift M) (Syn.shift r)) := Prf.hyp0
  have s : C ⊢[PRAAx] sndT (pairT (Syn.shift a * pw (Syn.shift M) (Syn.shift r))
      (pairT (succ (Syn.shift r)) (pairT (Syn.shift M) (Syn.shift x)))) ≐
      pairT (succ (Syn.shift r)) (pairT (Syn.shift M) (Syn.shift x)) := snd_pair _ _
  refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) s).eqTrans ?_
  refine (QB_at w Y G _ _ _ _).eqTrans ?_
  refine (congrMul (pr_peel w hM'.wk ha'.wk hu) (I_peel Y G hM'.wk ha'.wk hu)).eqTrans ?_
  refine .eqTrans ?_ (congrAdd (congrMul (.eqRefl _) (QB_at w Y G _ _ _ _))
    (congrAdd (congrMul (.eqRefl _) (GB_at w G _ _ _ _)) (.eqRefl _))).eqSymm
  ipra_ring

/-- `Q_{r+1}(Y) = Q_r(Y) W + G_r (∑ w Y)`. -/
theorem Q_succ {r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] Qt w Y G (succ r) M x ≐ Qt w Y G r M x * ap2 (sumF w) M x + Gt w G r M x * ap2 (sumF (w * Y)) M x := by
  refine (peel_sum (QB w Y G) r M _).eqTrans ((lin3 w (w * Y) (zero : PTm 2) (BlockSum.blkB (QB w Y G))
    (K₁ := Qt w Y G r M x) (K₂ := Gt w G r M x) (K₃ := zero) (p := x) (.allI (.impI ?_))).eqTrans ?_)
  rotate_left
  · ipra_ring
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  simp only [shift_pairT, ProductPower.shift_zero']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  have hQ : Syn.shift (Qt w Y G r M x) = Qt w Y G (Syn.shift r) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have hG : Syn.shift (Gt w G r M x) = Gt w G (Syn.shift r) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  rw [hp, hs, hQ, hG, inst2_mul', inst2_zero2]
  refine (block_Q w Y G hM'.wk Prf.hyp0).eqTrans ?_
  ipra_ring

theorem Q_zero (M x : PTm n) : Γ ⊢[PRAAx] Qt w Y G zero M x ≐ zero :=
  (one_bound _ _ _).eqTrans ((QB_at w Y G _ _ _ _).eqTrans ((congrMul (.eqRefl _) (sum_zero (IB Y G) _)).eqTrans (mul_zero _)))

theorem sum_w_one (M x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (w * (one : PTm 2))) M x ≐ ap2 (sumF w) M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_mul']
  have e : inst2 (one : PTm 2) (var 0) (Syn.shift x) = one := by simp [inst2]
  rw [e]
  ipra_ring

end Totals

/-- `thm:wald`: `W Q_N(X) = (∑ w X) Q_N(1)`, i.e. `E[∑_{j<T} X_j] = μ E[T]` for a stopping time whose tail
indicators `[T > j] = g(j, t mod M^j)` depend only on the first `j` coordinates. -/
theorem wald (w X G : PTm 2) {N M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] ap2 (sumF w) M x * Qt w X G N M x ≐ ap2 (sumF (w * X)) M x * Qt w (one : PTm 2) G N M x := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF w) (Syn.shift M) (Syn.shift x) * Qt w X G (var 0) (Syn.shift M) (Syn.shift x) ≐
      ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) * Qt w (one : PTm 2) G (var 0) (Syn.shift M) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Qt, Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact ((congrMul (.eqRefl _) (Q_zero w X G _ _)).eqTrans (mul_zero _)).eqTrans
        ((congrMul (.eqRefl _) (Q_zero w (one : PTm 2) G _ _)).eqTrans (mul_zero _)).eqSymm
    · simp only [Qt, Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let C : List (Fm PTm (n + 1)) := (ap2 (sumF w) (Syn.shift M) (Syn.shift x) * Qt w X G (var 0) (Syn.shift M) (Syn.shift x) ≐
          ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) * Qt w (one : PTm 2) G (var 0) (Syn.shift M) (Syn.shift x)) :: Γ.map Fm.shift
      have ih0 : C ⊢[PRAAx] ap2 (sumF w) (Syn.shift M) (Syn.shift x) * Qt w X G (var 0) (Syn.shift M) (Syn.shift x) ≐
          ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) * Qt w (one : PTm 2) G (var 0) (Syn.shift M) (Syn.shift x) := Prf.hyp0
      show C ⊢[PRAAx] _
      ipra_lc 𝔞 (ap2 (sumF w) (Syn.shift M) (Syn.shift x)) * natEq ih0 +
        𝔞 (ap2 (sumF w) (Syn.shift M) (Syn.shift x)) * natEq (Q_succ (Γ := C) w X G (r := var 0) (x := Syn.shift x) hM'.wk) -
        𝔞 (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) * natEq (Q_succ (Γ := C) w (one : PTm 2) G (r := var 0) (x := Syn.shift x) hM'.wk) -
        𝔞 (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) * 𝔞 (Gt w G (var 0) (Syn.shift M) (Syn.shift x)) * natEq (sum_w_one (Γ := C) w (Syn.shift M) (Syn.shift x))
  have h := Prf.allE N hall
  simp only [Qt, Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact h

end LeanProofs.IPRA.Probability.Wald
