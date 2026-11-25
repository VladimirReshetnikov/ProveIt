import IPRADerivations.Combinatorics.Vandermonde
import IPRADerivations.Combinatorics.CatalanHalving
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# The binomial theorem in two variables

`∑_{k ≤ m} C(m, k) x^k y^(m−k) = (x + y)^m`, the finite binomial identity behind polynomial
translation (`algebra/FTA_iPRA`: "Translation uses only the finite binomial identity";
`combinatorics/fibonacci_lucas_ipra`). `Combinatorics/BinomialTheorem` has the case `y = 1`.

The coefficients are the guarded `C(m, k)` of `Combinatorics/Vandermonde`, for which Pascal's rule
holds for every `k`. The summand reads `m, x, y` from the parameter `⟨m, ⟨x, y⟩⟩`.

* `binomial_two`: the identity for all `m, x, y`, by quantifier-free induction on `m`: shifting
  the index and Pascal's rule give `S(m + 1) = y S(m) + x S(m)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BinomialTwo

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_above gb_pascal)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.CatalanHalving (monus_succ_le)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies; variables `0 = k`, `1 = ⟨m, ⟨x, y⟩⟩` -/

/-- `C(m, k) x^k y^(m−k)`. -/
abbrev bt : PTm 2 := gb (fstT (var 1)) (var 0) * pw (fstT (sndT (var 1))) (var 0) *
  pw (sndT (sndT (var 1))) (monus (fstT (var 1)) (var 0))
/-- `C(m, k + 1) x^(k+1) y^(m−k)`. -/
abbrev aB : PTm 2 := gb (fstT (var 1)) (succ (var 0)) * pw (fstT (sndT (var 1))) (succ (var 0)) *
  pw (sndT (sndT (var 1))) (monus (fstT (var 1)) (var 0))
/-- `C(m, k) x^(k+1) y^(m−k)`. -/
abbrev cB : PTm 2 := gb (fstT (var 1)) (var 0) * pw (fstT (sndT (var 1))) (succ (var 0)) *
  pw (sndT (sndT (var 1))) (monus (fstT (var 1)) (var 0))
/-- `C(m, k) x^k y^(m+1−k)`. -/
abbrev dB : PTm 2 := gb (fstT (var 1)) (var 0) * pw (fstT (sndT (var 1))) (var 0) *
  pw (sndT (sndT (var 1))) (monus (succ (fstT (var 1))) (var 0))

/-- `S(m) = ∑_{k ≤ m} C(m, k) x^k y^(m−k)`. -/
abbrev S {n : ℕ} (M X Y : PTm n) : PTm n := ap2 (sumF bt) (succ M) (pairT M (pairT X Y))

theorem fM (M X Y : PTm n) : Γ ⊢[PRAAx] fstT (pairT M (pairT X Y)) ≐ M := fst_pair _ _
theorem fX (M X Y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (pairT M (pairT X Y))) ≐ X :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem fY (M X Y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (pairT M (pairT X Y))) ≐ Y :=
  (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)

theorem bt_at (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 bt k (pairT M (pairT X Y)) ≐ gb M k * pw X k * pw Y (monus M k) := by
  have h : inst2 bt k (pairT M (pairT X Y)) = gb (fstT (pairT M (pairT X Y))) k *
      pw (fstT (sndT (pairT M (pairT X Y)))) k *
      pw (sndT (sndT (pairT M (pairT X Y)))) (monus (fstT (pairT M (pairT X Y))) k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fM _ _ _) (.eqRefl _)) (congrPw (fX _ _ _) (.eqRefl _)))
    (congrPw (fY _ _ _) (congrMonus (fM _ _ _) (.eqRefl _)))

theorem aB_at (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 aB k (pairT M (pairT X Y)) ≐ gb M (succ k) * pw X (succ k) * pw Y (monus M k) := by
  have h : inst2 aB k (pairT M (pairT X Y)) = gb (fstT (pairT M (pairT X Y))) (succ k) *
      pw (fstT (sndT (pairT M (pairT X Y)))) (succ k) *
      pw (sndT (sndT (pairT M (pairT X Y)))) (monus (fstT (pairT M (pairT X Y))) k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fM _ _ _) (.eqRefl _)) (congrPw (fX _ _ _) (.eqRefl _)))
    (congrPw (fY _ _ _) (congrMonus (fM _ _ _) (.eqRefl _)))

theorem cB_at (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 cB k (pairT M (pairT X Y)) ≐ gb M k * pw X (succ k) * pw Y (monus M k) := by
  have h : inst2 cB k (pairT M (pairT X Y)) = gb (fstT (pairT M (pairT X Y))) k *
      pw (fstT (sndT (pairT M (pairT X Y)))) (succ k) *
      pw (sndT (sndT (pairT M (pairT X Y)))) (monus (fstT (pairT M (pairT X Y))) k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fM _ _ _) (.eqRefl _)) (congrPw (fX _ _ _) (.eqRefl _)))
    (congrPw (fY _ _ _) (congrMonus (fM _ _ _) (.eqRefl _)))

theorem dB_at (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 dB k (pairT M (pairT X Y)) ≐ gb M k * pw X k * pw Y (monus (succ M) k) := by
  have h : inst2 dB k (pairT M (pairT X Y)) = gb (fstT (pairT M (pairT X Y))) k *
      pw (fstT (sndT (pairT M (pairT X Y)))) k *
      pw (sndT (sndT (pairT M (pairT X Y)))) (monus (succ (fstT (pairT M (pairT X Y)))) k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fM _ _ _) (.eqRefl _)) (congrPw (fX _ _ _) (.eqRefl _)))
    (congrPw (fY _ _ _) (congrMonus (congrSucc (fM _ _ _)) (.eqRefl _)))

theorem shift_y (M X Y : PTm n) :
    Syn.shift (pairT M (pairT X Y)) = pairT (Syn.shift M) (pairT (Syn.shift X) (Syn.shift Y)) := by
  simp [Syn.shift]

/-! ## Pointwise identities -/

theorem p_pascal (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody bt) k (pairT (succ M) (pairT X Y)) ≐
      inst2 (addBody aB cB) k (pairT M (pairT X Y)) := by
  rw [inst2_shiftBody, inst2_addBody]
  refine (bt_at _ _ _ _).eqTrans (.eqTrans ?_ (congrAdd (aB_at _ _ _ _) (cB_at _ _ _ _)).eqSymm)
  refine (congrMul (congrMul (gb_pascal M k) (.eqRefl _)) (congrPw (.eqRefl _) (succ_monus_succ _ _))).eqTrans ?_
  ipra_ring

theorem p_x (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 cB k (pairT M (pairT X Y)) ≐ X * inst2 bt k (pairT M (pairT X Y)) := by
  refine (cB_at _ _ _ _).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (bt_at _ _ _ _)).eqSymm)
  refine (congrMul (congrMul (.eqRefl _) (pw_succ X k)) (.eqRefl _)).eqTrans ?_
  ipra_ring

theorem p_y {j M : PTm n} (X Y : PTm n) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] inst2 dB j (pairT M (pairT X Y)) ≐ Y * inst2 bt j (pairT M (pairT X Y)) := by
  refine (dB_at _ _ _ _).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (bt_at _ _ _ _)).eqSymm)
  refine (congrMul (.eqRefl _) ((congrPw (.eqRefl Y) (monus_succ_le hj)).eqTrans (pw_succ Y _))).eqTrans ?_
  ipra_ring

theorem p_shift (k M X Y : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody dB) k (pairT M (pairT X Y)) ≐ inst2 aB k (pairT M (pairT X Y)) := by
  rw [inst2_shiftBody]
  exact (dB_at _ _ _ _).eqTrans ((congrMul (.eqRefl _) (congrPw (.eqRefl _) (succ_monus_succ _ _))).eqTrans
    (aB_at _ _ _ _).eqSymm)

/-! ## The step -/

theorem binom2_step {M X Y : PTm n} (ih : Γ ⊢[PRAAx] S M X Y ≐ pw (X + Y) M) :
    Γ ⊢[PRAAx] S (succ M) X Y ≐ pw (X + Y) (succ M) := by
  have E0 := natEq (sum_shift (Γ := Γ) bt (succ M) (pairT (succ M) (pairT X Y)))
  have t0 := natEq ((bt_at (Γ := Γ) zero (succ M) X Y).eqTrans
    ((congrMul (congrMul (gb_zero _) (pw_zero X)) (congrPw (.eqRefl Y) (monus_zero _))).eqTrans
      ((congrMul (one_mul one) (.eqRefl _)).eqTrans (one_mul _))))
  have E1 := natEq (sum_congr_bounded (Γ := Γ) (shiftBody bt) (addBody aB cB) (pairT (succ M) (pairT X Y))
    (pairT M (pairT X Y)) (succ M) (.allI (.impI (by rw [shift_y, shift_y]; exact p_pascal _ _ _ _))))
  have E2 := natEq (sum_add (Γ := Γ) aB cB (succ M) (pairT M (pairT X Y)))
  have Ec' : Γ ⊢[PRAAx] ap2 (sumF cB) (succ M) (pairT M (pairT X Y)) ≐ X * S M X Y := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y]
    exact p_x _ _ _ _
  have Ec := natEq Ec'
  -- The `a` part through the body `dB`.
  have D1 := natEq (sum_shift (Γ := Γ) dB (succ M) (pairT M (pairT X Y)))
  have D2 := natEq (sum_succ' (Γ := Γ) dB (succ M) (pairT M (pairT X Y)))
  have d0 := natEq ((dB_at (Γ := Γ) zero M X Y).eqTrans
    ((congrMul (congrMul (gb_zero _) (pw_zero X)) (congrPw (.eqRefl Y) (monus_zero _))).eqTrans
      ((congrMul (one_mul one) (.eqRefl _)).eqTrans (one_mul _))))
  have dt := natEq ((dB_at (Γ := Γ) (succ M) M X Y).eqTrans
    ((congrMul (congrMul (gb_above (le_refl _)) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))))
  have Dy' : Γ ⊢[PRAAx] ap2 (sumF dB) (succ M) (pairT M (pairT X Y)) ≐ Y * S M X Y := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y]
    have e : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
    rw [e] at *
    exact p_y _ _ ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have Dy := natEq Dy'
  have Da := natEq (sum_congr_bounded (Γ := Γ) (shiftBody dB) aB (pairT M (pairT X Y)) (pairT M (pairT X Y))
    (succ M) (.allI (.impI (by rw [shift_y]; exact p_shift _ _ _ _))))
  have i := natEq ih; have P := natEq (pw_succ (Γ := Γ) (X + Y) M)
  apply deriveNat; ipra_simps
  linear_combination E0 + t0 + E1 + E2 + Ec - D1 + D2 - d0 + dt + Dy - Da + (𝔞(X) + 𝔞(Y)) * i - P

/-- Variables: `0 = m` (induction), `1 = x`, `2 = y`. -/
private abbrev b2F : Fm PTm 3 := S (var 0) (var 1) (var 2) ≐ pw (var 1 + var 2) (var 0)

theorem binom2_base (X Y : PTm n) : Γ ⊢[PRAAx] S zero X Y ≐ pw (X + Y) zero := by
  ipra_lc natEq (sum_succ' (Γ := Γ) bt zero (pairT zero (pairT X Y))) +
    natEq (sum_zero (Γ := Γ) bt (pairT zero (pairT X Y))) +
    natEq ((bt_at (Γ := Γ) zero zero X Y).eqTrans ((congrMul (congrMul (gb_zero _) (pw_zero X)) ((congrPw (.eqRefl Y) (monus_zero _)).eqTrans (pw_zero Y))).eqTrans ((congrMul (one_mul one) (.eqRefl _)).eqTrans (one_mul _)))) -
    natEq (pw_zero (Γ := Γ) (X + Y))

private theorem b2₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] b2F := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact binom2_base _ _
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact binom2_step Prf.hyp0

/-- `∑_{k ≤ m} C(m, k) x^k y^(m−k) = (x + y)^m`. -/
theorem binomial_two (M X Y : PTm n) : Γ ⊢[PRAAx] S M X Y ≐ pw (X + Y) M := by
  have h := inst (Γ := Γ) b2₀ (![M, X, Y] : Fin 3 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.BinomialTwo
