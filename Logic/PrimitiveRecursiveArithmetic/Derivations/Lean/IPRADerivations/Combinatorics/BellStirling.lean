import IPRADerivations.Combinatorics.StirlingBinomial
import IPRADerivations.Combinatorics.Bell
import IPRADerivations.Core.SumSplit

/-!
# Bell numbers as sums of Stirling numbers

Packet: `combinatorics/bell_numbers_ipra` (`B_n = ∑_k S(n, k)`: a partition of `[n]` has some number
`k` of blocks; this is also `𝓛(X^n) = B_n` for the umbral functional with `𝓛((X)_k) = 1`, by
`Combinatorics/StirlingPowers`). With `T(n) = ∑_{k ≤ n} S(n, k)`:

* `T_ext`: `∑_{k ≤ N} S(j, k) = T(j)` for `j ≤ N`, since `S(j, k) = 0` for `k > j`;
* `T_succ`: `T(n + 1) = ∑_{j ≤ n} C(n, j) T(j)`, from `S(n + 1, k + 1) = ∑_j C(n, j) S(j, k)`
  (`Combinatorics/StirlingBinomial`) by exchanging the sums (`Core/Fubini`);
* `bell_stirling`: `B_n = T(n)` for every `n`, by course-of-values induction against the Bell
  recurrence `eq:bell-binomial` of `Combinatorics/Bell`: the induction formula is that the
  violation count over `m ≤ n` vanishes.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellStirling

open_ipra
open LeanProofs.IPRA.Combinatorics.Stirling (stir stir_zero stir_above stir_succ_zero gle gle_of_le)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (congrStir)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb zB zsum inst2_z)
open LeanProofs.IPRA.Combinatorics.StirlingBinomial (uB U u_at shift_y stirling_binomial)
open LeanProofs.IPRA.Combinatorics.Bell (bell bell_zero bell_succ recB inst2_rec)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `S(n, k)`, over `0 = k`, `1 = n`. -/
abbrev tB : PTm 2 := stir (var 1) (var 0)
/-- `T(n) = ∑_{k ≤ n} S(n, k)`. -/
abbrev T {n : ℕ} (N : PTm n) : PTm n := ap2 (sumF tB) (succ N) N
/-- `C(n, j) S(j, k)`, over `0 = k`, `1 = j`, `2 = n`. -/
abbrev a3 : PTm 3 := gb (var 2) (var 1) * stir (var 1) (var 0)

theorem inst2_t (k N : PTm n) : inst2 tB k N = stir N k := by simp [inst2]
theorem inst3_a (k j N : PTm n) : inst3 a3 k j N = gb N j * stir j k := by simp [inst3]

/-! ## Extending the range -/

theorem T_ext {j N : PTm n} (h : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] ap2 (sumF tB) (succ N) j ≐ T j := by
  have eD : Γ ⊢[PRAAx] succ N ≐ succ j + monus N j := by
    ipra_lc natEq (eq_add_of_le h)
  refine (congrAp2 (sumF tB) eD (.eqRefl _)).eqTrans ((sum_split tB (succ j) (monus N j) j).eqTrans ?_)
  refine (congrAdd (.eqRefl _) ?_).eqTrans (add_zero _)
  refine (sum_congr_bounded (offB tB) zB (pairT (succ j) j) (pairT (succ j) j) _ (.allI (.impI ?_))).eqTrans (zsum _ _)
  rw [shift_y, inst2_z, inst2_offB, inst2_t]
  exact (congrStir (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _))).eqTrans (stir_above (le_add_right _ _))

/-! ## The recurrence of `T` -/

theorem row_pt (k N : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB a3) k (pairT (succ N) N) ≐ U N k := by
  rw [inst2_oB]
  refine (congrAp2 (sumF (rowB a3)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_y, shift_y, inst2_rowB, inst3_a]
  exact (congrMul (congrGb (snd_pair _ _) (.eqRefl _)) (congrStir (.eqRefl _) (fst_pair _ _))).eqTrans
    (u_at _ _ _).eqSymm

/-- `T(n + 1) = ∑_{j ≤ n} (∑_{k ≤ n} C(n, j) S(j, k))`. -/
theorem T_fub (N : PTm n) : Γ ⊢[PRAAx] T (succ N) ≐ ap2 (sumF (pB a3)) (succ N) (pairT (succ N) N) := by
  refine (sum_shift tB (succ N) (succ N)).eqTrans ?_
  rw [inst2_t]
  refine (congrAdd (stir_succ_zero N) ?_).eqTrans ((zero_add _).eqTrans (fubini a3 (succ N) (succ N) N))
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have e₁ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [shift_y, inst2_shiftBody, inst2_t, e₁]
  exact (stirling_binomial _ _).eqTrans (row_pt _ _).eqSymm

theorem col_pt {j N : PTm n} (h : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] inst2 (pB a3) j (pairT (succ N) N) ≐ gb N j * T j := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB a3)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  have sc : Γ ⊢[PRAAx] ap2 (sumF (colB a3)) (succ N) (pairT j N) ≐ gb N j * ap2 (sumF tB) (succ N) j := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have e₂ : Syn.shift (gb N j) = gb (Syn.shift N) (Syn.shift j) := by simp [Syn.shift]
    rw [shift_y, e₂, inst2_colB, inst3_a, inst2_t]
    exact congrMul (congrGb (snd_pair _ _) (fst_pair _ _)) (congrStir (fst_pair _ _) (.eqRefl _))
  exact sc.eqTrans (congrMul (.eqRefl _) (T_ext h))

/-! ## The course-of-values induction -/

/-- `1 ∸ [T(m) = B_m]`, over `0 = m`, `1 = x`. -/
abbrev vB : PTm 2 := monus one (eqb (T (var 0)) (bell (var 0)))

theorem inst2_v (m x : PTm n) : inst2 vB m x = monus one (eqb (T m) (bell m)) := by simp [inst2]

theorem eqT {N j : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (succ N) zero ≐ zero) (hj : Γ ⊢[PRAAx] lt j (succ N)) :
    Γ ⊢[PRAAx] T j ≐ bell j := by
  have z := sum_zero_elim vB ih hj
  rw [inst2_v] at z
  exact eq_of_viol z

theorem rec_pt {N j : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (succ N) zero ≐ zero) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] inst2 (pB a3) j (pairT (succ N) N) ≐ inst2 recB j N := by
  rw [inst2_rec]
  refine (col_pt hj).eqTrans ((congrMul (.eqRefl _) (eqT ih ((succ_monus_succ _ _).eqTrans hj))).eqTrans ?_)
  exact congrMul ((congrMul (gle_of_le hj) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)

theorem T_succ {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (succ N) zero ≐ zero) :
    Γ ⊢[PRAAx] T (succ N) ≐ bell (succ N) := by
  refine (T_fub N).eqTrans (.eqTrans ?_ (bell_succ N).eqSymm)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have ih' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF vB) (succ (Syn.shift N)) zero ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  have e₁ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [shift_y, e₁]
  exact rec_pt ih'.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)

theorem T_zero : Γ ⊢[PRAAx] T (zero : PTm n) ≐ bell zero := by
  have s := sum_succ' (Γ := Γ) tB zero (zero : PTm n)
  rw [inst2_t] at s
  exact s.eqTrans ((congrAdd (sum_zero _ _) stir_zero).eqTrans ((zero_add _).eqTrans bell_zero.eqSymm))

theorem v_base : Γ ⊢[PRAAx] ap2 (sumF vB) (succ zero) (zero : PTm n) ≐ zero := by
  have s := sum_succ' (Γ := Γ) vB zero (zero : PTm n)
  rw [inst2_v] at s
  exact s.eqTrans ((congrAdd (sum_zero _ _) (viol_of_eq T_zero)).eqTrans (add_zero _))

theorem v_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (succ N) zero ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF vB) (succ (succ N)) zero ≐ zero := by
  have s := sum_succ' (Γ := Γ) vB (succ N) (zero : PTm n)
  rw [inst2_v] at s
  exact s.eqTrans ((congrAdd ih (viol_of_eq (T_succ ih))).eqTrans (add_zero _))

/-- Variable: `0 = N`. -/
private abbrev vF : Fm PTm 1 := ap2 (sumF vB) (succ (var 0)) zero ≐ zero

private theorem v₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] vF := by
  ipra_ind [subst_ap2]
  · exact v_base
  · exact v_step Prf.hyp0

/-- `B_n = ∑_{k ≤ n} S(n, k)`. -/
theorem bell_stirling (N : PTm n) : Γ ⊢[PRAAx] T N ≐ bell N := by
  have h := inst (Γ := Γ) v₀ (![N] : Fin 1 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact eqT h ((succ_monus_succ _ _).eqTrans (le_refl _))

end LeanProofs.IPRA.Combinatorics.BellStirling
