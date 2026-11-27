import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.Header

/-!
# Domination of a product of two sums, one index at a time

A reusable rule of the embedding framework, used for
`combinatorics/bell_numbers_ipra`, `lem:coefficient-logconcave`, whose proof pairs the indices
`j < k` of a double sum ("Expand the product ..., subtract the two resulting products, and pair
indices `j, k`", `eq:paired-logconcavity`).

For four families `p, q, r, s`, if

* `r_j s_j ≤ p_j q_j` for every `j`, and
* `r_j s_k + r_k s_j ≤ p_j q_k + p_k q_j` for every pair `j < k`,

then `(Σ r)(Σ s) ≤ (Σ p)(Σ q)`. The proof is an induction on the common upper limit `L` whose
step needs the pair condition only against the new index:

`(P + p)(Q + q) − (R + r)(S + s) = (PQ − RS) + [(P q + p Q) − (R s + r S)] + (pq − rs)`,

and `R s + r S = Σ_{j<L} (r_j s + r s_j)`. So no double sum and no interchange of summations is
needed.

* `sum_lin_le`: `Σ F · a + b · Σ G ≤ Σ H · c + d · Σ K` from the same inequality between the
  terms;
* `sum_trunc`: a sum whose terms vanish from `M` on is the sum up to `M`;
* `dom_alg`: the algebra of the step;
* `dom_step`: the step, for bodies `p, q, r, s` with a common parameter.
-/

namespace LeanProofs.IPRA.Foundations.ProductSumDomination

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## A linear inequality between four sums -/

/-- The induction formula of `sum_lin_le`; variable `0` is the upper limit. -/
abbrev linLeF (F G H K : PTm 2) (a b c d x N : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift N) ⟶
    le (ap2 (sumF F) (var 0) (Syn.shift x) * Syn.shift a +
        Syn.shift b * ap2 (sumF G) (var 0) (Syn.shift x))
      (ap2 (sumF H) (var 0) (Syn.shift x) * Syn.shift c +
        Syn.shift d * ap2 (sumF K) (var 0) (Syn.shift x))

/-- `Σ F · a + b · Σ G ≤ Σ H · c + d · Σ K` from the same inequality between the terms. -/
theorem sum_lin_le (F G H K : PTm 2) {a b c d x N : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 F (var 0) (Syn.shift x) * Syn.shift a +
          Syn.shift b * inst2 G (var 0) (Syn.shift x))
        (inst2 H (var 0) (Syn.shift x) * Syn.shift c +
          Syn.shift d * inst2 K (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF F) N x * a + b * ap2 (sumF G) N x)
      (ap2 (sumF H) N x * c + d * ap2 (sumF K) N x) := by
  refine le_congr (congrAdd (mul_comm _ _) (.eqRefl _)) (congrAdd (mul_comm _ _) (.eqRefl _))
    (sum_weighted_pair_le F G H K a b c d x x x x N (.allI (.impI ?_)))
  exact le_congr (congrAdd (mul_comm _ _) (.eqRefl _)) (congrAdd (mul_comm _ _) (.eqRefl _))
    (.impE hp.allOpen.wk Prf.hyp0)

/-! ## Truncation of a sum -/

/-- The step of `sum_trunc`, in any context. -/
theorem trunc_step (f : PTm 2) {M K N x : PTm n}
    (ih : Γ ⊢[PRAAx] le M K ⟶ (le K N ⟶ (ap2 (sumF f) K x ≐ ap2 (sumF f) M x)))
    (hz : Γ ⊢[PRAAx] lt K N ⟶ (le M K ⟶ (inst2 f K x ≐ zero)))
    (h₁ : Γ ⊢[PRAAx] le M (succ K)) (h₂ : Γ ⊢[PRAAx] le (succ K) N) :
    Γ ⊢[PRAAx] ap2 (sumF f) (succ K) x ≐ ap2 (sumF f) M x := by
  refine .orE (lt_or_eq_of_le h₁) ?_ ?_
  · have hMK : (lt M (succ K) :: Γ) ⊢[PRAAx] le M K :=
      (succ_monus_succ M K).eqSymm.eqTrans Prf.hyp0
    have a := Prf.impE (Prf.impE ih.wk hMK) (le_trans (le_succ_self K) h₂.wk)
    have z := Prf.impE (Prf.impE hz.wk h₂.wk) hMK
    exact (sum_succ' f K x).eqTrans ((congrAdd a z).eqTrans (add_zero _))
  · exact congrAp2 _ (Prf.hyp0 (Γ := Γ) (φ := M ≐ succ K)).eqSymm (.eqRefl _)

/-- The induction formula of `sum_trunc`; variable `0` is the upper limit. -/
abbrev truncF (f : PTm 2) (M N x : PTm n) : Fm PTm (n + 1) :=
  le (Syn.shift M) (var 0) ⟶ (le (var 0) (Syn.shift N) ⟶
    (ap2 (sumF f) (var 0) (Syn.shift x) ≐ ap2 (sumF f) (Syn.shift M) (Syn.shift x)))

/-- A sum whose terms vanish from `M` on is the sum up to `M`. -/
theorem sum_trunc (f : PTm 2) {M N x : PTm n} (h : Γ ⊢[PRAAx] le M N)
    (hz : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (le (Syn.shift M) (var 0) ⟶ (inst2 f (var 0) (Syn.shift x) ≐ zero)))) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF f) M x := by
  have hall : Γ ⊢[PRAAx] Fm.all (truncF f M N x) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _, trivial⟩) [subst_le, subst_ap2]
    · refine .impI (.impI ?_)
      have m0 : (le zero N :: le M zero :: Γ) ⊢[PRAAx] M ≐ zero :=
        le_antisymm (Prf.hyp1 (Γ := Γ) (φ := le M zero) (ψ := le zero N)) (zero_le M)
      exact congrAp2 _ m0.eqSymm (.eqRefl _)
    · refine .impI (.impI ?_)
      exact trunc_step f (N := Syn.shift N) (.hyp (by simp)) hz.allOpen.wk.wk.wk
        (.hyp (by simp)) Prf.hyp0
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact .impE (.impE h2 h) (le_refl N)

/-! ## The domination step -/

/-- The algebra of the step. -/
theorem dom_alg {P Q R S p q r s : PTm n} (ih : Γ ⊢[PRAAx] le (R * S) (P * Q))
    (hd : Γ ⊢[PRAAx] le (r * s) (p * q)) (hc : Γ ⊢[PRAAx] le (R * s + r * S) (P * q + p * Q)) :
    Γ ⊢[PRAAx] le ((R + r) * (S + s)) ((P + p) * (Q + q)) := by
  refine le_of_eq_add (d := monus (P * Q) (R * S) + monus (p * q) (r * s) +
    monus (P * q + p * Q) (R * s + r * S)) ?_
  ipra_lc natEq (eq_add_of_le ih) + natEq (eq_add_of_le hd) + natEq (eq_add_of_le hc)

theorem shift_inst2 (f : PTm 2) (i x : PTm n) :
    Syn.shift (inst2 f i x) = inst2 f (Syn.shift i) (Syn.shift x) := by
  simp only [Syn.shift, inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- One more index: `(Σ_{j<L} r)(Σ_{j<L} s) ≤ (Σ_{j<L} p)(Σ_{j<L} q)`, the diagonal condition
at `L` and the pair conditions `(j, L)`, `j < L`, give the inequality for `L + 1`. -/
theorem dom_step (p q r s : PTm 2) {L w : PTm n}
    (ih : Γ ⊢[PRAAx] le (ap2 (sumF r) L w * ap2 (sumF s) L w)
      (ap2 (sumF p) L w * ap2 (sumF q) L w))
    (hd : Γ ⊢[PRAAx] le (inst2 r L w * inst2 s L w) (inst2 p L w * inst2 q L w))
    (ho : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶
      le (inst2 r (var 0) (Syn.shift w) * inst2 s (Syn.shift L) (Syn.shift w) +
          inst2 r (Syn.shift L) (Syn.shift w) * inst2 s (var 0) (Syn.shift w))
        (inst2 p (var 0) (Syn.shift w) * inst2 q (Syn.shift L) (Syn.shift w) +
          inst2 p (Syn.shift L) (Syn.shift w) * inst2 q (var 0) (Syn.shift w)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF r) (succ L) w * ap2 (sumF s) (succ L) w)
      (ap2 (sumF p) (succ L) w * ap2 (sumF q) (succ L) w) := by
  have ho' : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶
      le (inst2 r (var 0) (Syn.shift w) * Syn.shift (inst2 s L w) +
          Syn.shift (inst2 r L w) * inst2 s (var 0) (Syn.shift w))
        (inst2 p (var 0) (Syn.shift w) * Syn.shift (inst2 q L w) +
          Syn.shift (inst2 p L w) * inst2 q (var 0) (Syn.shift w))) := by
    simp only [shift_inst2]
    exact ho
  have hc := sum_lin_le r s p q ho'
  exact le_congr (congrMul (sum_succ' r L w).eqSymm (sum_succ' s L w).eqSymm)
    (congrMul (sum_succ' p L w).eqSymm (sum_succ' q L w).eqSymm) (dom_alg ih hd hc)

end LeanProofs.IPRA.Foundations.ProductSumDomination

export_ipra Foundations.ProductSumDomination (sum_trunc)
