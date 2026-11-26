import IPRADerivations.Combinatorics.StirlingPowers
import IPRADerivations.Combinatorics.Vandermonde
import IPRADerivations.Probability.Independence

/-!
# The binomial recurrence of the Stirling numbers

Packet: `combinatorics/bell_numbers_ipra` (the identity behind `lem:finite-shift` with `k = 1`,
`𝓛(X f(X)) = 𝓛(f(X + 1))`, on the falling-factorial basis; and the step from the Stirling
numbers to the Bell recurrence `eq:bell-binomial`):

  `S(n + 1, k + 1) = ∑_{j ≤ n} C(n, j) S(j, k)`.

With `U(n, k)` the right side, Pascal's rule and the Stirling recurrence give
`U(n + 1, k) = (k + 1) U(n, k) + U(n, k − 1)`, the recurrence of `S(n + 2, k + 1)`.

* `stir_rec`: `S(n + 1, k + 1) = (k + 1) S(n, k + 1) + S(n, k)` for every `k`;
* `U_step`: `U(n + 1, k) = (k + 1) U(n, k) + L(n, k)` with `L(n, k + 1) = U(n, k)`, `L(n, 0) = 0`;
* `stirling_binomial`: the identity for all `n, k`. The induction is on `n`, with the formula that
  the violation count over `k < R` vanishes, since the step at `k` uses the hypothesis at `k` and
  at `k − 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.StirlingBinomial

open_ipra
open LeanProofs.IPRA.Combinatorics.Stirling
  (stir stir_zero stir_above stir_succ_zero stir_succ_succ sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (congrStir)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_above gb_pascal zB zsum inst2_z)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `S(n + 1, k + 1) = (k + 1) S(n, k + 1) + S(n, k)` for every `k`. -/
theorem stir_rec (N K : PTm n) : Γ ⊢[PRAAx] stir (succ N) (succ K) ≐ succ K * stir N (succ K) + stir N K := by
  refine .orE (lt_or_le N K) ?_ (stir_succ_succ Prf.hyp0)
  have h : (lt N K :: Γ) ⊢[PRAAx] le (succ N) K := Prf.hyp0
  have z₁ := stir_above ((succ_monus_succ _ _).eqTrans h : (lt N K :: Γ) ⊢[PRAAx] le (succ (succ N)) (succ K))
  have z₂ := stir_above (le_trans h (le_succ_self K))
  have z₃ := stir_above h
  exact z₁.eqTrans ((add_zero _).eqSymm.eqTrans ((congrAdd ((mul_zero _).eqSymm.eqTrans
    (congrMul (.eqRefl _) z₂.eqSymm)) z₃.eqSymm)))

theorem stir_zero_succ (K : PTm n) : Γ ⊢[PRAAx] stir zero (succ K) ≐ zero :=
  stir_above ((succ_monus_succ _ _).eqTrans (zero_le K))

/-! ## Bodies; variables `0 = j`, `1 = ⟨n, k⟩` -/

/-- `C(n, j) S(j, k)`. -/
abbrev uB : PTm 2 := gb (fstT (var 1)) (var 0) * stir (var 0) (sndT (var 1))
/-- `C(n, j) S(j + 1, k)`. -/
abbrev sB : PTm 2 := gb (fstT (var 1)) (var 0) * stir (succ (var 0)) (sndT (var 1))
/-- `k C(n, j) S(j, k)`. -/
abbrev wB : PTm 2 := sndT (var 1) * uB
/-- `[k ≥ 1] C(n, j) S(j, k − 1)`. -/
abbrev lB : PTm 2 := sg (sndT (var 1)) * (gb (fstT (var 1)) (var 0) * stir (var 0) (pred (sndT (var 1))))

/-- `U(n, k) = ∑_{j ≤ n} C(n, j) S(j, k)`. -/
abbrev U {n : ℕ} (N K : PTm n) : PTm n := ap2 (sumF uB) (succ N) (pairT N K)
/-- `L(n, k) = ∑_{j ≤ n} [k ≥ 1] C(n, j) S(j, k − 1)`. -/
abbrev L {n : ℕ} (N K : PTm n) : PTm n := ap2 (sumF lB) (succ N) (pairT N K)

theorem u_at (j N K : PTm n) : Γ ⊢[PRAAx] inst2 uB j (pairT N K) ≐ gb N j * stir j K := by
  have h : inst2 uB j (pairT N K) = gb (fstT (pairT N K)) j * stir j (sndT (pairT N K)) := by simp [inst2]
  rw [h]; exact congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrStir (.eqRefl _) (snd_pair _ _))

theorem s_at (j N K : PTm n) : Γ ⊢[PRAAx] inst2 sB j (pairT N K) ≐ gb N j * stir (succ j) K := by
  have h : inst2 sB j (pairT N K) = gb (fstT (pairT N K)) j * stir (succ j) (sndT (pairT N K)) := by simp [inst2]
  rw [h]; exact congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrStir (.eqRefl _) (snd_pair _ _))

theorem w_at (j N K : PTm n) : Γ ⊢[PRAAx] inst2 wB j (pairT N K) ≐ K * inst2 uB j (pairT N K) := by
  have h : inst2 wB j (pairT N K) = sndT (pairT N K) * inst2 uB j (pairT N K) := by simp [inst2]
  rw [h]; exact congrMul (snd_pair _ _) (.eqRefl _)

theorem l_at (j N K : PTm n) :
    Γ ⊢[PRAAx] inst2 lB j (pairT N K) ≐ sg K * (gb N j * stir j (pred K)) := by
  have h : inst2 lB j (pairT N K) =
      sg (sndT (pairT N K)) * (gb (fstT (pairT N K)) j * stir j (pred (sndT (pairT N K)))) := by simp [inst2]
  rw [h]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (snd_pair _ _)))
    (congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrStir (.eqRefl _) (congrPred (snd_pair _ _))))

theorem shift_y (N K : PTm n) : Syn.shift (pairT N K) = pairT (Syn.shift N) (Syn.shift K) := by simp [Syn.shift]

/-! ## The step -/

theorem pascal_pt (j N K : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody uB) j (pairT (succ N) K) ≐ inst2 (addBody (shiftBody uB) sB) j (pairT N K) := by
  rw [inst2_shiftBody, inst2_addBody, inst2_shiftBody]
  refine (u_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (u_at _ _ _) (s_at _ _ _)).eqSymm)
  refine (congrMul (gb_pascal N j) (.eqRefl _)).eqTrans ?_
  ipra_ring

theorem ringA (g A B c : PTm n) : Γ ⊢[PRAAx] g * (c * A + B) ≐ c * (g * A) + one * (g * B) := by
  ipra_ring

theorem split_pt (j N K : PTm n) :
    Γ ⊢[PRAAx] inst2 sB j (pairT N K) ≐ inst2 (addBody wB lB) j (pairT N K) := by
  rw [inst2_addBody]
  refine (s_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (w_at _ _ _) (l_at _ _ _)).eqSymm)
  refine .orE (zero_or_succ K) ?_ ?_
  · have e : ((K ≐ zero) :: Γ) ⊢[PRAAx] K ≐ zero := Prf.hyp0
    have z₁ : ((K ≐ zero) :: Γ) ⊢[PRAAx] stir (succ j) K ≐ zero :=
      (congrStir (.eqRefl _) e).eqTrans (stir_succ_zero j)
    have z₂ : ((K ≐ zero) :: Γ) ⊢[PRAAx] sg K ≐ zero :=
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) e)).eqTrans sg_zero
    refine ((congrMul (.eqRefl _) z₁).eqTrans (mul_zero _)).eqTrans ?_
    exact (add_zero zero).eqSymm.eqTrans (congrAdd ((zero_mul _).eqSymm.eqTrans (congrMul e.eqSymm (.eqRefl _)))
      ((zero_mul _).eqSymm.eqTrans (congrMul z₂.eqSymm (.eqRefl _))))
  · have e : ((K ≐ succ (pred K)) :: Γ) ⊢[PRAAx] K ≐ succ (pred K) := Prf.hyp0
    have r := (congrStir (.eqRefl (succ j)) e).eqTrans (stir_rec j (pred K))
    have o : ((K ≐ succ (pred K)) :: Γ) ⊢[PRAAx] sg K ≐ one :=
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) e)).eqTrans (sg_succ _)
    have st : ((K ≐ succ (pred K)) :: Γ) ⊢[PRAAx] stir j K ≐ stir j (succ (pred K)) := congrStir (.eqRefl _) e
    refine (congrMul (.eqRefl _) r).eqTrans ((ringA _ _ _ _).eqTrans ?_)
    exact congrAdd (congrMul e.eqSymm ((congrMul (.eqRefl _) st.eqSymm).eqTrans (u_at _ _ _).eqSymm))
      (congrMul o.eqSymm (.eqRefl _))

/-- `U(n + 1, k) = (k + 1) U(n, k) + L(n, k)`. -/
theorem U_step (N K : PTm n) : Γ ⊢[PRAAx] U (succ N) K ≐ succ K * U N K + L N K := by
  have E0 := natEq (sum_shift (Γ := Γ) uB (succ N) (pairT (succ N) K))
  have t0 := natEq ((u_at (Γ := Γ) zero (succ N) K).eqTrans ((congrMul (gb_zero _) (.eqRefl _)).eqTrans (one_mul _)))
  have E1 := natEq (sum_congr_bounded (Γ := Γ) (shiftBody uB) (addBody (shiftBody uB) sB) (pairT (succ N) K)
    (pairT N K) (succ N) (.allI (.impI (by rw [shift_y, shift_y]; exact pascal_pt _ _ _))))
  have E2 := natEq (sum_add (Γ := Γ) (shiftBody uB) sB (succ N) (pairT N K))
  have F1 := natEq (sum_shift (Γ := Γ) uB (succ N) (pairT N K))
  have F2 := natEq (sum_succ' (Γ := Γ) uB (succ N) (pairT N K))
  have f0 := natEq ((u_at (Γ := Γ) zero N K).eqTrans ((congrMul (gb_zero _) (.eqRefl _)).eqTrans (one_mul _)))
  have ft := natEq ((u_at (Γ := Γ) (succ N) N K).eqTrans ((congrMul (gb_above (le_refl _)) (.eqRefl _)).eqTrans
    (zero_mul _)))
  have G1 := natEq (sum_congr_bounded (Γ := Γ) sB (addBody wB lB) (pairT N K) (pairT N K) (succ N)
    (.allI (.impI (by rw [shift_y]; exact split_pt _ _ _))))
  have G2 := natEq (sum_add (Γ := Γ) wB lB (succ N) (pairT N K))
  have G3' : Γ ⊢[PRAAx] ap2 (sumF wB) (succ N) (pairT N K) ≐ K * U N K := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y]; exact w_at _ _ _
  have G3 := natEq G3'
  apply deriveNat; ipra_simps
  linear_combination E0 + t0 + E1 + E2 - F1 + F2 - f0 + ft + G1 + G2 + G3

theorem L_succ (N K : PTm n) : Γ ⊢[PRAAx] L N (succ K) ≐ U N K := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_y, shift_y]
  refine (l_at _ _ _).eqTrans (.eqTrans ?_ (u_at _ _ _).eqSymm)
  exact (congrMul (sg_succ _) (congrMul (.eqRefl _) (congrStir (.eqRefl _) (pred_succ _)))).eqTrans (one_mul _)

theorem L_zero (N : PTm n) : Γ ⊢[PRAAx] L N zero ≐ zero := by
  refine (sum_congr_bounded lB zB (pairT N zero) (pairT N zero) _ (.allI (.impI ?_))).eqTrans (zsum _ _)
  have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [shift_y, inst2_z, ez]
  exact (l_at _ _ _).eqTrans ((congrMul sg_zero (.eqRefl _)).eqTrans (zero_mul _))

/-- The step of the identity: from `S(n + 1, k + 1) = U(n, k)` and `S(n + 1, k) = L(n, k)`. -/
theorem sb_step {N K : PTm n} (h₁ : Γ ⊢[PRAAx] stir (succ N) (succ K) ≐ U N K)
    (h₀ : Γ ⊢[PRAAx] stir (succ N) K ≐ L N K) :
    Γ ⊢[PRAAx] stir (succ (succ N)) (succ K) ≐ U (succ N) K :=
  (stir_rec (succ N) K).eqTrans ((congrAdd (congrMul (.eqRefl _) h₁) h₀).eqTrans (U_step N K).eqSymm)

theorem sb_base (K : PTm n) : Γ ⊢[PRAAx] stir (succ zero) (succ K) ≐ U zero K := by
  refine (stir_rec zero K).eqTrans ?_
  ipra_lc (𝔞(K) + 1) * natEq (stir_zero_succ (Γ := Γ) K) - natEq (sum_succ' (Γ := Γ) uB zero (pairT zero K)) -
    natEq (sum_zero (Γ := Γ) uB (pairT zero K)) -
    natEq ((u_at (Γ := Γ) zero zero K).eqTrans ((congrMul (gb_zero _) (.eqRefl _)).eqTrans (one_mul _)))

/-! ## The induction on `n` -/

/-- `1 ∸ [S(n + 1, k + 1) = U(n, k)]`, over `0 = k`, `1 = n`. -/
abbrev violB : PTm 2 := monus one (eqb (stir (succ (var 1)) (succ (var 0))) (U (var 1) (var 0)))

theorem inst2_viol (k N : PTm n) :
    inst2 violB k N = monus one (eqb (stir (succ N) (succ k)) (U N k)) := by simp [inst2]

theorem eq_at {N s R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R N ≐ zero) (hs : Γ ⊢[PRAAx] lt s R) :
    Γ ⊢[PRAAx] stir (succ N) (succ s) ≐ U N s := by
  have z := sum_zero_elim violB ih hs
  rw [inst2_viol] at z
  exact eq_of_viol z

theorem viol_point {N k R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R N ≐ zero) (hk : Γ ⊢[PRAAx] lt k R) :
    Γ ⊢[PRAAx] inst2 violB k (succ N) ≐ zero := by
  rw [inst2_viol]
  refine viol_of_eq (sb_step (eq_at ih hk) ?_)
  refine .orE (zero_or_succ k) ?_ ?_
  · have e : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    exact (congrStir (.eqRefl _) e).eqTrans ((stir_succ_zero N).eqTrans
      ((L_zero N).eqSymm.eqTrans (congrAp2 (sumF lB) (.eqRefl _) (congrPairT (.eqRefl _) e.eqSymm))))
  · have e : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have l₀ : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] lt (pred k) R :=
      le_trans (le_congr e (.eqRefl _) (le_succ_self k)) hk.wk
    have h := eq_at ih.wk l₀
    exact (congrStir (.eqRefl _) e).eqTrans (h.eqTrans ((L_succ N (pred k)).eqSymm.eqTrans
      (congrAp2 (sumF lB) (.eqRefl _) (congrPairT (.eqRefl _) e.eqSymm))))

theorem viol_step {N R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R N ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF violB) R (succ N) ≐ zero := by
  refine (sum_congr_bounded violB zB (succ N) N R (.allI (.impI ?_))).eqTrans (zsum _ _)
  have ih' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF violB) (Syn.shift R) (Syn.shift N) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  have e₁ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [e₁, inst2_z]
  exact viol_point ih'.wk Prf.hyp0

theorem viol_base (R : PTm n) : Γ ⊢[PRAAx] ap2 (sumF violB) R zero ≐ zero := by
  refine (sum_congr_bounded violB zB zero zero R (.allI (.impI ?_))).eqTrans (zsum _ _)
  have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [ez, inst2_z, inst2_viol]
  exact viol_of_eq (sb_base _)

/-- Variables: `0 = n` (induction), `1 = R`. -/
private abbrev vF : Fm PTm 2 := ap2 (sumF violB) (var 1) (var 0) ≐ zero

private theorem v₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] vF := by
  ipra_ind [subst_ap2]
  · exact viol_base _
  · exact viol_step Prf.hyp0

/-- `S(n + 1, k + 1) = ∑_{j ≤ n} C(n, j) S(j, k)`. -/
theorem stirling_binomial (N K : PTm n) : Γ ⊢[PRAAx] stir (succ N) (succ K) ≐ U N K := by
  have h := inst (Γ := Γ) v₀ (![N, succ K] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact eq_at h ((succ_monus_succ _ _).eqTrans (le_refl _))

end LeanProofs.IPRA.Combinatorics.StirlingBinomial
