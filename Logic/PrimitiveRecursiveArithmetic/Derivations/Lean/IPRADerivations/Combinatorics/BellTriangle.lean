import IPRADerivations.Combinatorics.BellBounds
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.LinearCombination

/-!
# The Bell triangle

Packet: `combinatorics/bell_numbers_ipra`, Proposition `prop:bell-triangle`. With the closed form
`T(n, k) = ∑_{i≤k} C(k, i) B_{n−i}`:

* `tri_zero`: `T(n, 0) = B_n`;
* `tri_step`: `T(n + 1, k + 1) = T(n + 1, k) + T(n, k)` (the defining addition rule);
* `tri_diag`: `T(n, n) = B_{n+1}`, so each row starts with the previous row's last entry.

`tri_step` peels the first and last terms and applies Pascal's rule `C(k+1, i+1) = C(k, i) + C(k, i+1)`
strictly inside (`i < k`; the quotient definition of `C` is not zero above the diagonal at `k = 0`).
`tri_diag` reflects the sum (`Core/SumReflect`), uses `C(n, n − i) = C(n, i)` and the recurrence.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellTriangle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (bell recB inst2_rec bell_succ monus_monus)
open LeanProofs.IPRA.Combinatorics.BellBounds (congrBell binom_zero')
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden bden_pos bden_self quo_of_eq pascal_step binom_rem_zero)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Binomial facts -/

theorem binom_self' (k : PTm n) : Γ ⊢[PRAAx] binom k k ≐ one := quo_of_eq (bden_pos _ _) (bden_self _)

theorem pascal_lt {j k : PTm n} (h : Γ ⊢[PRAAx] lt j k) :
    Γ ⊢[PRAAx] binom (succ k) (succ j) ≐ binom k j + binom k (succ j) :=
  quo_of_eq (bden_pos _ _) (pascal_step h (binom_rem_zero (le_of_lt h)) (binom_rem_zero h))

/-- `C(N, N − i) = C(N, i)` for `i ≤ N`. -/
theorem binom_symm {i N : PTm n} (h : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] binom N (monus N i) ≐ binom N i := by
  refine congrAp2 quoF (.eqRefl _) ?_
  exact (congrMul (.eqRefl _) (congrAp2 factF (monus_monus h) (.eqRefl _))).eqTrans (mul_comm _ _)

/-! ## The triangle -/

/-- `C(fst y, i) B_{snd y − i}`. -/
abbrev tB : PTm 2 := binom (fstT (var 1)) (var 0) * bell (monus (sndT (var 1)) (var 0))
/-- `C(fst y, i + 1) B_{snd y − i}`. -/
abbrev sB : PTm 2 := binom (fstT (var 1)) (succ (var 0)) * bell (monus (sndT (var 1)) (var 0))

theorem inst2_tB (i y : PTm n) : inst2 tB i y = binom (fstT y) i * bell (monus (sndT y) i) := by simp [inst2]
theorem inst2_sB (i y : PTm n) : inst2 sB i y = binom (fstT y) (succ i) * bell (monus (sndT y) i) := by
  simp [inst2]

/-- `T(N, K) = ∑_{i≤K} C(K, i) B_{N−i}`. -/
abbrev tri (N K : PTm n) : PTm n := ap2 (sumF tB) (succ K) (pairT K N)

theorem shift_succ' (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

/-- The first term `C(K, 0) B_{N}`. -/
theorem first_term (K N : PTm n) : Γ ⊢[PRAAx] inst2 tB zero (pairT K N) ≐ bell N := by
  rw [inst2_tB]
  exact (congrMul ((congrBinom (fst_pair _ _) (.eqRefl _)).eqTrans (binom_zero' _))
    (congrBell ((congrMonus (snd_pair _ _) (.eqRefl _)).eqTrans (monus_zero _)))).eqTrans (one_mul _)

/-- The last term `C(K, K) B_{N−K}`. -/
theorem last_term (K N : PTm n) : Γ ⊢[PRAAx] inst2 tB K (pairT K N) ≐ bell (monus N K) := by
  rw [inst2_tB]
  exact (congrMul ((congrBinom (fst_pair _ _) (.eqRefl _)).eqTrans (binom_self' _))
    (congrBell (congrMonus (snd_pair _ _) (.eqRefl _)))).eqTrans (one_mul _)

theorem tri_zero (N : PTm n) : Γ ⊢[PRAAx] tri N zero ≐ bell N :=
  (sum_succ' tB zero _).eqTrans ((congrAdd (sum_zero _ _) (first_term _ _)).eqTrans (zero_add _))

/-- The defining addition rule `T(m + 1, k + 1) = T(m + 1, k) + T(m, k)`. -/
theorem tri_step (m k : PTm n) : Γ ⊢[PRAAx] tri (succ m) (succ k) ≐ tri (succ m) k + tri m k := by
  -- `T(m+1, k+1) = B_{m+1} + (A + S) + B_{m−k}`.
  have x₁ : Γ ⊢[PRAAx] ap2 (sumF (shiftBody tB)) k (pairT (succ k) (succ m)) ≐
      ap2 (sumF tB) k (pairT k m) + ap2 (sumF sB) k (pairT k m) := by
    refine (sum_congr_bounded (shiftBody tB) (addBody tB sB) _ (pairT k m) k (.allI (.impI ?_))).eqTrans
      (sum_add tB sB k (pairT k m))
    rw [inst2_shiftBody, inst2_addBody, inst2_tB, inst2_tB, inst2_sB, shift_pairT, shift_pairT, shift_succ',
      shift_succ']
    generalize Syn.shift k = k' at *
    generalize Syn.shift m = m'
    refine (congrMul ((congrBinom (fst_pair _ _) (.eqRefl _)).eqTrans (pascal_lt Prf.hyp0))
      (congrBell ((congrMonus (snd_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ _ _)))).eqTrans ?_
    refine .eqTrans ?_ (congrAdd (congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrBell (congrMonus
      (snd_pair _ _) (.eqRefl _)))) (congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrBell (congrMonus
      (snd_pair _ _) (.eqRefl _))))).eqSymm
    ipra_ring
  have e₁ : Γ ⊢[PRAAx] tri (succ m) (succ k) ≐
      bell (succ m) + (ap2 (sumF tB) k (pairT k m) + ap2 (sumF sB) k (pairT k m)) + bell (monus m k) :=
    (sum_succ' tB (succ k) _).eqTrans (congrAdd ((sum_shift tB k _).eqTrans (congrAdd (first_term _ _) x₁))
      ((last_term _ _).eqTrans (congrBell (succ_monus_succ _ _))))
  -- `T(m+1, k) = B_{m+1} + S`.
  have x₂ : Γ ⊢[PRAAx] ap2 (sumF (shiftBody tB)) k (pairT k (succ m)) ≐ ap2 (sumF sB) k (pairT k m) := by
    refine sum_congr_bounded (shiftBody tB) sB _ (pairT k m) k (.allI (.impI ?_))
    rw [inst2_shiftBody, inst2_tB, inst2_sB, shift_pairT, shift_pairT, shift_succ']
    exact congrMul (congrBinom ((fst_pair _ _).eqTrans (fst_pair _ _).eqSymm) (.eqRefl _))
      (congrBell ((congrMonus (snd_pair _ _) (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans
        (congrMonus (snd_pair _ _).eqSymm (.eqRefl _)))))
  have e₂ : Γ ⊢[PRAAx] tri (succ m) k ≐ bell (succ m) + ap2 (sumF sB) k (pairT k m) :=
    (sum_shift tB k _).eqTrans (congrAdd (first_term _ _) x₂)
  -- `T(m, k) = A + B_{m−k}`.
  have e₃ : Γ ⊢[PRAAx] tri m k ≐ ap2 (sumF tB) k (pairT k m) + bell (monus m k) :=
    (sum_succ' tB k _).eqTrans (congrAdd (.eqRefl _) (last_term _ _))
  ipra_lc natEq e₁ - natEq e₂ - natEq e₃

/-- `T(N, N) = B_{N+1}`. -/
theorem tri_diag (N : PTm n) : Γ ⊢[PRAAx] tri N N ≐ bell (succ N) := by
  refine (sum_reflect tB (succ N) (pairT N N)).eqTrans (.eqTrans ?_ (bell_succ N).eqSymm)
  refine sum_congr_bounded (rflBody tB) recB _ N (succ N) (.allI (.impI ?_))
  rw [inst2_rflBody, inst2_tB, inst2_rec, shift_pairT, shift_pairT, shift_succ']
  generalize Syn.shift N = N'
  have hv : (lt (var 0) (succ N') :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) N' :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have eI : (lt (var 0) (succ N') :: Γ.map Fm.shift) ⊢[PRAAx]
      monus (fstT (pairT (succ N') (pairT N' N'))) (succ (var 0)) ≐ monus N' (var 0) :=
    (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ _ _)
  have eB : (lt (var 0) (succ N') :: Γ.map Fm.shift) ⊢[PRAAx] fstT (sndT (pairT (succ N') (pairT N' N'))) ≐ N' :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have eC : (lt (var 0) (succ N') :: Γ.map Fm.shift) ⊢[PRAAx] sndT (sndT (pairT (succ N') (pairT N' N'))) ≐ N' :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  exact congrMul ((congrBinom eB eI).eqTrans (binom_symm hv))
    (congrBell ((congrMonus eC eI).eqTrans (monus_monus hv)))

/-- `prop:bell-triangle`: variables `0 = n`, `1 = k`. -/
abbrev bellTriangleFormula : Fm PTm 2 :=
  (tri (var 0) zero ≐ bell (var 0)) ⋏
    ((tri (succ (var 0)) (succ (var 1)) ≐ tri (succ (var 0)) (var 1) + tri (var 0) (var 1)) ⋏
      (tri (var 0) (var 0) ≐ bell (succ (var 0))))

theorem bell_triangle : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 bellTriangleFormula :=
  closeUniv 2 (.andI (tri_zero _) (.andI (tri_step _ _) (tri_diag _)))

end LeanProofs.IPRA.Combinatorics.BellTriangle
