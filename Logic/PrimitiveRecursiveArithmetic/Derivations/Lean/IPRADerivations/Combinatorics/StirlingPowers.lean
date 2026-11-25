import IPRADerivations.Combinatorics.Stirling
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# Powers as sums of falling factorials

Packet: `combinatorics/bell_numbers_ipra` (`eq:power-falling`): `X^n = ∑_{k ≤ n} S(n, k) (X)_k`,
derived for natural `X` from the recurrence of `Combinatorics/Stirling`.

* `ff X k = (X)_k = ∏_{j<k} (X ∸ j)`; it vanishes for `k > X`, because the factor `j = X` is `0`;
* `ff_mul`: `X (X)_k = (X)_{k+1} + k (X)_k`, the identity the packet compares with the Stirling
  recurrence (both cases `k ≤ X` and `k > X`);
* `stirling_powers`: `∑_{k ≤ n} S(n, k) (X)_k = X^n` for every `n` and `X`, by quantifier-free
  induction on `n`. In the step the top term `(n + 1) S(n, n + 1)` vanishes and the bottom term
  `S(n + 1, 0)` vanishes, which lets the two index shifts cancel.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.StirlingPowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (nth)
open LeanProofs.IPRA.Combinatorics.Stirling
  (stir stir_zero stir_above stir_succ_zero stir_succ_succ RF congrNth)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Falling factorials -/

/-- The factor `X ∸ j`; variables `0 = j`, `1 = X`. -/
abbrev ffB : PTm 2 := monus (var 1) (var 0)
/-- `(X)_k = ∏_{j<k} (X ∸ j)`. -/
abbrev ff {n : ℕ} (X k : PTm n) : PTm n := ap2 (prodF ffB) k X

theorem ff_zero (X : PTm n) : Γ ⊢[PRAAx] ff X zero ≐ one := prod_zero _ _

theorem ff_succ (X k : PTm n) : Γ ⊢[PRAAx] ff X (succ k) ≐ ff X k * monus X k := by
  have h := prod_succ (Γ := Γ) ffB k X
  simpa using h

theorem ff_zero_above {X k : PTm n} (h : Γ ⊢[PRAAx] lt X k) : Γ ⊢[PRAAx] ff X k ≐ zero := by
  have e : inst2 ffB X X = monus X X := by simp [inst2]
  exact prod_zero_of ffB h (by rw [e]; exact monus_self X)

/-- `X (X)_k = (X)_{k+1} + k (X)_k`. -/
theorem ff_mul (X k : PTm n) : Γ ⊢[PRAAx] X * ff X k ≐ ff X (succ k) + k * ff X k := by
  refine .orE (lt_or_le X k) ?_ ?_
  · ipra_lc (𝔞(X) - 𝔞(k) - 𝔞(monus X k)) * natEq (ff_zero_above (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt X k))) -
      natEq (ff_succ (Γ := lt X k :: Γ) X k)
  · ipra_lc 𝔞(ff X k) * natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le k X))) -
      natEq (ff_succ (Γ := le k X :: Γ) X k)

/-! ## Bodies; variables `0 = k`, `1 = ⟨N, X⟩` -/

/-- `S(N, k) (X)_k`. -/
abbrev tB : PTm 2 := stir (fstT (var 1)) (var 0) * ff (sndT (var 1)) (var 0)
/-- `k S(N, k) (X)_k`. -/
abbrev wB : PTm 2 := var 0 * tB
/-- `S(N, k) (X)_{k+1}`. -/
abbrev uB : PTm 2 := stir (fstT (var 1)) (var 0) * ff (sndT (var 1)) (succ (var 0))

theorem congrStir {N N' K K' : PTm n} (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K') :
    Γ ⊢[PRAAx] stir N K ≐ stir N' K' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus hK hN)) (congrNth (congrAp1 RF hN) (congrMonus hN hK))

theorem congrFF {X X' k k' : PTm n} (hX : Γ ⊢[PRAAx] X ≐ X') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] ff X k ≐ ff X' k' := congrAp2 (prodF ffB) hk hX

theorem inst2_t (k y : PTm n) : inst2 tB k y = stir (fstT y) k * ff (sndT y) k := by simp [inst2]
theorem inst2_w (k y : PTm n) : inst2 wB k y = k * (stir (fstT y) k * ff (sndT y) k) := by simp [inst2]
theorem inst2_u (k y : PTm n) : inst2 uB k y = stir (fstT y) k * ff (sndT y) (succ k) := by simp [inst2]

theorem tB_at (k N X : PTm n) : Γ ⊢[PRAAx] inst2 tB k (pairT N X) ≐ stir N k * ff X k := by
  rw [inst2_t]; exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrFF (snd_pair _ _) (.eqRefl _))

theorem wB_at (k N X : PTm n) : Γ ⊢[PRAAx] inst2 wB k (pairT N X) ≐ k * (stir N k * ff X k) := by
  rw [inst2_w]
  exact congrMul (.eqRefl _) (congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrFF (snd_pair _ _) (.eqRefl _)))

theorem uB_at (k N X : PTm n) : Γ ⊢[PRAAx] inst2 uB k (pairT N X) ≐ stir N k * ff X (succ k) := by
  rw [inst2_u]; exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrFF (snd_pair _ _) (.eqRefl _))

/-! ## The two index shifts -/

/-- `∑_{k ≤ N} (k + 1) S(N, k + 1) (X)_{k+1} = ∑_{k ≤ N} k S(N, k) (X)_k`. -/
theorem wsum (N X : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (shiftBody wB)) (succ N) (pairT N X) ≐ ap2 (sumF wB) (succ N) (pairT N X) := by
  have w₀ : Γ ⊢[PRAAx] inst2 wB zero (pairT N X) ≐ zero := by rw [inst2_w]; exact zero_mul _
  have wt : Γ ⊢[PRAAx] inst2 wB (succ N) (pairT N X) ≐ zero :=
    (wB_at _ _ _).eqTrans ((congrMul (.eqRefl _) ((congrMul (stir_above (le_refl _)) (.eqRefl _)).eqTrans
      (zero_mul _))).eqTrans (mul_zero _))
  ipra_lc -natEq (sum_shift (Γ := Γ) wB (succ N) (pairT N X)) + natEq (sum_succ' (Γ := Γ) wB (succ N) (pairT N X)) -
    natEq w₀ + natEq wt

theorem step_pt {k N : PTm n} (X : PTm n) (h : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] inst2 (shiftBody tB) k (pairT (succ N) X) ≐ inst2 (addBody (shiftBody wB) uB) k (pairT N X) := by
  rw [inst2_shiftBody, inst2_addBody, inst2_shiftBody]
  refine (tB_at _ _ _).eqTrans ((congrMul (stir_succ_succ h) (.eqRefl _)).eqTrans ?_)
  refine .eqTrans ?_ (congrAdd (wB_at _ _ _) (uB_at _ _ _)).eqSymm
  ipra_ring

theorem x_pt (k N X : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody uB wB) k (pairT N X) ≐ X * inst2 tB k (pairT N X) := by
  rw [inst2_addBody]
  ipra_lc natEq (uB_at (Γ := Γ) k N X) + natEq (wB_at (Γ := Γ) k N X) - 𝔞(X) * natEq (tB_at (Γ := Γ) k N X) -
    𝔞(Stirling.gle k N) * 𝔞(nth (Stirling.row N) (monus N k)) * natEq (ff_mul (Γ := Γ) X k)

/-! ## The identity -/

/-- `∑_{k ≤ N} S(N, k) (X)_k`. -/
abbrev Am {n : ℕ} (N X : PTm n) : PTm n := ap2 (sumF tB) (succ N) (pairT N X)

theorem pf_base (X : PTm n) : Γ ⊢[PRAAx] Am zero X ≐ pw X zero := by
  ipra_lc natEq (sum_succ' (Γ := Γ) tB zero (pairT zero X)) + natEq (sum_zero (Γ := Γ) tB (pairT zero X)) +
    natEq ((tB_at (Γ := Γ) zero zero X).eqTrans ((congrMul stir_zero (ff_zero X)).eqTrans (one_mul one))) -
    natEq (pw_zero (Γ := Γ) X)

theorem pf_step {N X : PTm n} (ih : Γ ⊢[PRAAx] Am N X ≐ pw X N) :
    Γ ⊢[PRAAx] Am (succ N) X ≐ pw X (succ N) := by
  have E0 := natEq (sum_shift (Γ := Γ) tB (succ N) (pairT (succ N) X))
  have T0 := natEq ((tB_at (Γ := Γ) zero (succ N) X).eqTrans
    ((congrMul (stir_succ_zero N) (.eqRefl _)).eqTrans (zero_mul _)))
  have e₁ : Syn.shift (pairT (succ N) X) = pairT (succ (Syn.shift N)) (Syn.shift X) := by simp [Syn.shift]
  have e₂ : Syn.shift (pairT N X) = pairT (Syn.shift N) (Syn.shift X) := by simp [Syn.shift]
  have e₃ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have E1' : Γ ⊢[PRAAx] ap2 (sumF (shiftBody tB)) (succ N) (pairT (succ N) X) ≐
      ap2 (sumF (addBody (shiftBody wB) uB)) (succ N) (pairT N X) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [e₁, e₂]
    rw [e₃] at *
    exact step_pt _ ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have E2 := natEq (sum_add (Γ := Γ) (shiftBody wB) uB (succ N) (pairT N X))
  have E3 := natEq (wsum (Γ := Γ) N X)
  have E4 := natEq (sum_add (Γ := Γ) uB wB (succ N) (pairT N X))
  have E5' : Γ ⊢[PRAAx] ap2 (sumF (addBody uB wB)) (succ N) (pairT N X) ≐ X * Am N X := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [e₂]
    exact x_pt _ _ _
  have E1 := natEq E1'; have E5 := natEq E5'
  have i := natEq ih; have P := natEq (pw_succ (Γ := Γ) X N)
  apply deriveNat; ipra_simps
  linear_combination E0 + T0 + E1 + E2 + E3 - E4 + E5 + 𝔞(X) * i - P

/-- Variables: `0 = N` (induction), `1 = X`. -/
private abbrev pfF : Fm PTm 2 := Am (var 0) (var 1) ≐ pw (var 1) (var 0)

private theorem pf₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] pfF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    exact pf_base _
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    exact pf_step Prf.hyp0

/-- `eq:power-falling`: `∑_{k ≤ N} S(N, k) (X)_k = X^N`. -/
theorem stirling_powers (N X : PTm n) : Γ ⊢[PRAAx] Am N X ≐ pw X N := by
  have h := inst (Γ := Γ) pf₀ (![N, X] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.StirlingPowers
