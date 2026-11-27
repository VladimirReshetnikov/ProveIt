import IPRADerivations.Probability.ExpectationCorollaries

/-!
# The finite union bound and expected-utility maximization

Packet: `probability/expected_value_ipra_2026-11-16`.

* `union_bound` (`cor:union-bound`): for events (indicator bodies) `A_j(i)`, `j < r`, with union
  indicator `sg(∑_j A_j(i))`, `∑_i w_i [∪_j A_j](i) ≤ ∑_{j<r} ∑_i w_i A_j(i)`: pointwise
  `sg(s) ≤ s`, then the finite Fubini exchange;
* a primitive-recursive argmax: for a value table `V(a)`, `a < K`, the running maximum
  `M(k + 1) = M(k) + (V(k) ∸ M(k))` and the argmax `A(k + 1) = A(k) + [V(k) > M(k)] (k ∸ A(k))` satisfy
  `V(b) ≤ M(K)` for `b < K` (`mx_upper`) and `A(K) < K`, `V(A(K)) = M(K)` for `K ≥ 1` (`ag_attains`);
* `argmax` and `expected_utility` (`thm:expected-utility`): for a utility table `u(a, s)` and a state
  law `w`, the selected action `a* = A(K)` satisfies `∑_s w_s u(a, s) ≤ ∑_s w_s u(a*, s)` for every
  action `a < K`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.UnionUtility

open_ipra
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The union bound -/

alias congrSg' := Common.congrSg

alias shift_inst2' := Independence.shift_inst2

theorem sg_le_self (s : PTm n) : Γ ⊢[PRAAx] le (sg s) s := by
  refine .orE (zero_or_succ s) ?_ ?_
  · exact le_congr ((congrSg' Prf.hyp0).eqTrans sg_zero).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr ((congrSg' Prf.hyp0).eqTrans (sg_succ _)).eqSymm Prf.hyp0.eqSymm
      (le_of_eq_add (d := pred s) (by ipra_ring))

section Union

variable (w : PTm 2) (A : PTm 3)

/-- `w(i, x) A(i, j, x)`, over `0 = i`, `1 = j`, `2 = x`. -/
abbrev aw : PTm 3 := Syn.subst ![var 0, var 2] w * A
/-- `w(i, x) · sg(∑_{j<r} A(i, j, x))`, over `0 = i`, `1 = ⟨r, x⟩`. -/
abbrev UB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] w * sg (oB A)

theorem inst2_UB (i y : PTm n) : inst2 (UB w A) i y = inst2 w i (sndT y) * sg (inst2 (oB A) i y) := by
  have hf : Syn.subst ![i, y] (Syn.subst ![var 0, sndT (var 1)] w) = inst2 w i (sndT y) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, UB, PTm.subst_mul, hf]
  simp [inst2]

theorem inst3_aw (i j x : PTm n) : inst3 (aw w A) i j x = inst2 w i x * inst3 A i j x := by
  have hf : Syn.subst ![i, j, x] (Syn.subst ![var 0, var 2] w) = inst2 w i x := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, aw, PTm.subst_mul, hf]

/-- The weighted row: `∑_{j<r} w(i) A(i, j) = w(i) ∑_{j<r} A(i, j)`. -/
theorem row_aw (i r x : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB (aw w A)) i (pairT r x) ≐ inst2 w i x * inst2 (oB A) i (pairT r x) := by
  rw [inst2_oB, inst2_oB]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT r x) ≐ r := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT r x) ≐ x := snd_pair _ _
  refine (congrAp2 (sumF (rowB (aw w A))) f₁ (congrPairT (.eqRefl _) s₁)).eqTrans ?_
  refine .eqTrans ?_ (congrMul (.eqRefl _) (congrAp2 (sumF (rowB A)) f₁ (congrPairT (.eqRefl _) s₁))).eqSymm
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_rowB, inst2_rowB, shift_pairT, shift_inst2']
  refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
  rw [inst3_aw]
  exact congrMul (.eqRefl _) (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqSymm

/-- `cor:union-bound`: `∑_i w_i sg(∑_{j<r} A_j(i)) ≤ ∑_{j<r} ∑_{i<N} w_i A_j(i)`. -/
theorem union_bound (N r x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (UB w A)) N (pairT r x)) (ap2 (sumF (pB (aw w A))) r (pairT N x)) := by
  refine le_trans ?_ (le_congr (.eqRefl _) (fubini (aw w A) N r x) (le_refl _))
  refine sum_le _ _ _ _ (.allI (.impI ?_))
  rw [inst2_UB, shift_pairT]
  refine le_congr (congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _)).eqSymm (.eqRefl _)) (row_aw w A _ _ _).eqSymm ?_
  exact le_mul_mono' (sg_le_self _)
where
  le_mul_mono' {Δ : List (Fm PTm (n + 1))} {a b c : PTm (n + 1)} (h : Δ ⊢[PRAAx] le a b) :
      Δ ⊢[PRAAx] le (c * a) (c * b) :=
    AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl c) h

end Union

/-! ## A primitive-recursive argmax -/

section Argmax

variable (V : PTm 2)

/-- The running maximum step, over `0 = k`, `1 = M(k)`, `2 = x`. -/
def mxStep : PTm 3 := var 1 + monus (Syn.subst ![var 0, var 2] V) (var 1)
abbrev mxF : PR 2 := rec2 zero (mxStep V)
/-- `M(K, x) = max_{a<K} V(a, x)` (and `0` for `K = 0`). -/
abbrev Mx (K x : PTm n) : PTm n := ap2 (mxF V) K x

/-- The argmax step, over `0 = k`, `1 = A(k)`, `2 = x`. -/
def agStep : PTm 3 :=
  var 1 + sg (monus (Syn.subst ![var 0, var 2] V) (ap2 (mxF V) (var 0) (var 2))) * monus (var 0) (var 1)
abbrev agF : PR 2 := rec2 zero (agStep V)
/-- The selected index `A(K, x)`. -/
abbrev Ag (K x : PTm n) : PTm n := ap2 (agF V) K x

theorem subV (k m x : PTm n) : Syn.subst ![k, m, x] (Syn.subst ![var 0, var 2] V) = inst2 V k x := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp

theorem mx_zero (x : PTm n) : Γ ⊢[PRAAx] Mx V zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (mxStep V) x
  simpa using h

theorem mx_succ (k x : PTm n) : Γ ⊢[PRAAx] Mx V (succ k) x ≐ Mx V k x + monus (inst2 V k x) (Mx V k x) := by
  have h := rec2_succ (Γ := Γ) zero (mxStep V) k x
  have e : Syn.subst ![k, ap2 (mxF V) k x, x] (mxStep V) = Mx V k x + monus (inst2 V k x) (Mx V k x) := by
    simp only [mxStep, PTm.subst_add, PTm.subst_monus, subV]; simp
  rw [e] at h; exact h

theorem ag_zero (x : PTm n) : Γ ⊢[PRAAx] Ag V zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (agStep V) x
  simpa using h

theorem ag_succ (k x : PTm n) :
    Γ ⊢[PRAAx] Ag V (succ k) x ≐ Ag V k x + sg (monus (inst2 V k x) (Mx V k x)) * monus k (Ag V k x) := by
  have h := rec2_succ (Γ := Γ) zero (agStep V) k x
  have e : Syn.subst ![k, ap2 (agF V) k x, x] (agStep V) =
      Ag V k x + sg (monus (inst2 V k x) (Mx V k x)) * monus k (Ag V k x) := by
    simp only [agStep, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subV, subst_ap2]; simp
  rw [e] at h; exact h

/-- `m + (v ∸ m)` is at least `m` and at least `v`. -/
theorem max_ge (m v : PTm n) : Γ ⊢[PRAAx] le m (m + monus v m) ⋏ le v (m + monus v m) :=
  .andI (le_add_right _ _) (Common.le_add_monus v m)

/-- Variables `0 = K`, `1 = b`, `2 = x`. -/
private abbrev upF : Fm PTm 3 := lt (var 1) (var 0) ⟶ le (inst2 V (var 1) (var 2)) (Mx V (var 0) (var 2))

private theorem up₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] upF V := by
  ipra_ind (⟨lt_QF _ _, le_QF _ _⟩) [upF, subst_le, subst_lt, subst_ap2, subst_inst2]
  · exact .impI (lt_zero_absurd _ Prf.hyp0)
  · refine .impI ?_
    have mg := max_ge (Γ := lt (var 1) (succ (var 0)) :: [upF V]) (Mx V (var 0) (var 2)) (inst2 V (var 0) (var 2))
    refine le_congr (.eqRefl _) (mx_succ V _ _).eqSymm ?_
    refine .orE (lt_succ_cases Prf.hyp0) ?_ ?_
    · exact le_trans (.impE hyp2 Prf.hyp0) (Prf.andE₁ mg).wk
    · exact le_congr (congrInst2 V Prf.hyp0.eqSymm (.eqRefl _)) (.eqRefl _) (Prf.andE₂ mg).wk

/-- `V(b) ≤ M(K)` for `b < K`. -/
theorem mx_upper {K b x : PTm n} (h : Γ ⊢[PRAAx] lt b K) : Γ ⊢[PRAAx] le (inst2 V b x) (Mx V K x) := by
  have i := inst (Γ := Γ) (up₀ V) (![K, b, x] : Fin 3 → PTm n)
  simp only [upF, Fm.subst_imp, subst_le, subst_lt, subst_ap2, subst_inst2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_zero] at i
  exact .impE i h

/-- Variables `0 = k`, `1 = x`: the argmax of the first `k + 1` values attains the maximum. -/
private abbrev atF : Fm PTm 2 :=
  lt (Ag V (succ (var 0)) (var 1)) (succ (var 0)) ⋏ (inst2 V (Ag V (succ (var 0)) (var 1)) (var 1) ≐ Mx V (succ (var 0)) (var 1))

private theorem at₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] atF V := by
  ipra_ind (⟨lt_QF _ _, trivial⟩) [atF, subst_lt, subst_ap2, subst_inst2]
  · have a1 : ([] : List (Fm PTm 1)) ⊢[PRAAx] Ag V (succ zero) (var 0) ≐ zero :=
      (ag_succ V zero (var 0)).eqTrans ((congrAdd (ag_zero V _) ((congrMul (.eqRefl _)
        ((congrMonus (.eqRefl _) (ag_zero V _)).eqTrans (monus_self _))).eqTrans (mul_zero _))).eqTrans (add_zero _))
    have m1 : ([] : List (Fm PTm 1)) ⊢[PRAAx] Mx V (succ zero) (var 0) ≐ inst2 V zero (var 0) :=
      (mx_succ V zero (var 0)).eqTrans ((congrAdd (mx_zero V _) ((congrMonus (.eqRefl _) (mx_zero V _)).eqTrans
        (monus_zero _))).eqTrans (zero_add _))
    exact .andI (lt_congr a1.eqSymm (.eqRefl _) (zero_lt_succ _))
      ((congrInst2 V a1 (.eqRefl _)).eqTrans m1.eqSymm)
  · let D : List (Fm PTm 2) := [atF V]
    have ih1 : D ⊢[PRAAx] lt (Ag V (succ (var 0)) (var 1)) (succ (var 0)) := Prf.andE₁ Prf.hyp0
    have ih2 : D ⊢[PRAAx] inst2 V (Ag V (succ (var 0)) (var 1)) (var 1) ≐ Mx V (succ (var 0)) (var 1) := Prf.andE₂ Prf.hyp0
    have as := ag_succ (Γ := D) V (succ (var 0)) (var 1)
    have ms := mx_succ (Γ := D) V (succ (var 0)) (var 1)
    refine .orE (lt_or_le (Mx V (succ (var 0)) (var 1)) (inst2 V (succ (var 0)) (var 1))) ?_ ?_
    · -- a new maximum at `k + 1`
      let C : List (Fm PTm 2) := lt (Mx V (succ (var 0)) (var 1)) (inst2 V (succ (var 0)) (var 1)) :: D
      have h : C ⊢[PRAAx] lt (Mx V (succ (var 0)) (var 1)) (inst2 V (succ (var 0)) (var 1)) := Prf.hyp0
      have a2 : C ⊢[PRAAx] Ag V (succ (succ (var 0))) (var 1) ≐ succ (var 0) :=
        as.wk.eqTrans ((congrAdd (.eqRefl _) ((congrMul (sg_lt h) (.eqRefl _)).eqTrans (one_mul _))).eqTrans
          (eq_add_of_le (le_of_lt ih1.wk)).eqSymm)
      have m2 : C ⊢[PRAAx] Mx V (succ (succ (var 0))) (var 1) ≐ inst2 V (succ (var 0)) (var 1) :=
        ms.wk.eqTrans (eq_add_of_le (le_of_lt h)).eqSymm
      exact .andI (lt_congr a2.eqSymm (.eqRefl _) (le_refl _)) ((congrInst2 V a2 (.eqRefl _)).eqTrans m2.eqSymm)
    · let C : List (Fm PTm 2) := le (inst2 V (succ (var 0)) (var 1)) (Mx V (succ (var 0)) (var 1)) :: D
      have h : C ⊢[PRAAx] le (inst2 V (succ (var 0)) (var 1)) (Mx V (succ (var 0)) (var 1)) := Prf.hyp0
      have a2 : C ⊢[PRAAx] Ag V (succ (succ (var 0))) (var 1) ≐ Ag V (succ (var 0)) (var 1) :=
        as.wk.eqTrans ((congrAdd (.eqRefl _) (ExpectationCorollaries.zml (sg_le h) _)).eqTrans (add_zero _))
      have m2 : C ⊢[PRAAx] Mx V (succ (succ (var 0))) (var 1) ≐ Mx V (succ (var 0)) (var 1) :=
        ms.wk.eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _))
      exact .andI (lt_congr a2.eqSymm (.eqRefl _) (le_trans ih1.wk (le_succ_self _)))
        ((congrInst2 V a2 (.eqRefl _)).eqTrans (ih2.wk.eqTrans m2.eqSymm))

/-- For `K ≥ 1`, the selected index is `< K` and attains the maximum. -/
theorem ag_attains (k x : PTm n) :
    Γ ⊢[PRAAx] lt (Ag V (succ k) x) (succ k) ⋏ (inst2 V (Ag V (succ k) x) x ≐ Mx V (succ k) x) := by
  have i := inst (Γ := Γ) (at₀ V) (![k, x] : Fin 2 → PTm n)
  simpa using i

/-- The argmax: for `K = k + 1 ≥ 1`, `a* = A(K) < K` and `V(b) ≤ V(a*)` for every `b < K`. -/
theorem argmax {k b x : PTm n} (hb : Γ ⊢[PRAAx] lt b (succ k)) :
    Γ ⊢[PRAAx] lt (Ag V (succ k) x) (succ k) ⋏ le (inst2 V b x) (inst2 V (Ag V (succ k) x) x) :=
  .andI (Prf.andE₁ (ag_attains V k x))
    (le_congr (.eqRefl _) (Prf.andE₂ (ag_attains V k x)).eqSymm (mx_upper V hb))

end Argmax

/-- `w(s, x) u(a, s, x)`, over `0 = a`, `1 = s`, `2 = x`. -/
abbrev aw' (w : PTm 2) (u : PTm 3) : PTm 3 := Syn.subst ![var 1, var 2] w * u

/-- `thm:expected-utility`: for a utility table `u(a, s, x)` and state weights `w(s, x)` on `s < S`,
the selected action `a* = A(K)` (`K = k + 1` actions) satisfies
`∑_{s<S} w_s u(b, s) ≤ ∑_{s<S} w_s u(a*, s)` for every action `b < K`. -/
theorem expected_utility (w : PTm 2) (u : PTm 3) {k b S x : PTm n} (hb : Γ ⊢[PRAAx] lt b (succ k)) :
    Γ ⊢[PRAAx] lt (Ag (oB (aw' w u)) (succ k) (pairT S x)) (succ k) ⋏
      le (inst2 (oB (aw' w u)) b (pairT S x)) (inst2 (oB (aw' w u)) (Ag (oB (aw' w u)) (succ k) (pairT S x)) (pairT S x)) :=
  argmax (oB (aw' w u)) hb

end LeanProofs.IPRA.Probability.UnionUtility
