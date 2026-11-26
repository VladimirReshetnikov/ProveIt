import IPRADerivations.Core.BoundedSums

/-!
# The one-dimensional Sperner lemma (`dimension_invariance_ipra`)

The packet's proof of dimension invariance rests on the cubical Sperner parity
lemma (`dimension_invariance.tex`), whose one-dimensional case is the base of
its induction: along a path `0, 1, …, N` labelled by `0` and `1`, the number of
edges whose ends carry different labels has the parity of `ℓ(N) − ℓ(0)`. In
particular it is odd when `ℓ(0) = 0` and `ℓ(N) = 1`.

In iPRA the labelling is `ℓ(i) = par (f i)` for an arbitrary unary primitive
recursive symbol `f`, so every labelling by `0, 1` is covered. With
`C(N) = ∑_{i<N} |ℓ(i + 1) − ℓ(i)|`, derived for every `f` and every `N`:

* `par (C(N) + ℓ(0)) = ℓ(N)`, by induction on `N`;
* `ℓ(0) = 0 → ℓ(N) = 1 → par C(N) = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.Sperner

open_ipra

variable (f : PR 1) {n : ℕ} {Γ : List (Fm PTm n)}

/-- The label `ℓ(i) = par (f i)`. -/
abbrev ℓ (i : PTm n) : PTm n := par (ap1 f i)

/-- `|x − y|`. -/
abbrev dist (x y : PTm n) : PTm n := monus x y + monus y x

/-- The change indicator of the edge `(i, i + 1)`; variables `0 = i`, `1` unused. -/
abbrev changeBody : PTm 2 := dist (ℓ f (succ (var 0))) (ℓ f (var 0))

/-- `C(N) = ∑_{i<N} |ℓ(i + 1) − ℓ(i)|`. -/
abbrev C (N : PTm n) : PTm n := ap2 (sumF (changeBody f)) N zero

variable {f}

theorem par_par (x : PTm n) : Γ ⊢[PRAAx] par (par x) ≐ par x := by
  refine .orE (par_cases x) ?_ ?_
  · exact (congrAp1 parF Prf.hyp0).eqTrans (par_zero.eqTrans Prf.hyp0.eqSymm)
  · refine (congrAp1 parF Prf.hyp0).eqTrans ?_
    exact ((par_succ _).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _))).eqTrans
      Prf.hyp0.eqSymm

/-- The parity invariant; variable `0 = N`. -/
abbrev invFormula : Fm PTm 1 := par (C f (var 0) + ℓ f zero) ≐ ℓ f (var 0)

/-- `par (S x) = 1 ∸ par x`, and the values of `1 ∸ v` on `{0, 1}`. -/
private theorem flip {x v w : PTm n} (hx : Γ ⊢[PRAAx] par x ≐ v) (hv : Γ ⊢[PRAAx] (v ≐ zero) ⋎ (v ≐ one))
    (hw : Γ ⊢[PRAAx] (w ≐ zero) ⋎ (w ≐ one)) (hne : Γ ⊢[PRAAx] neg (v ≐ w)) :
    Γ ⊢[PRAAx] par (succ x) ≐ w := by
  refine (par_succ x).eqTrans ((congrMonus (.eqRefl _) hx).eqTrans ?_)
  refine .orE hv ?_ ?_
  · refine .orE hw.wk ?_ ?_
    · exact .botE _ (.impE hne.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))
    · exact (congrMonus (.eqRefl _) Prf.hyp1).eqTrans ((monus_zero _).eqTrans Prf.hyp0.eqSymm)
  · refine .orE hw.wk ?_ ?_
    · exact (congrMonus (.eqRefl _) Prf.hyp1).eqTrans ((monus_self _).eqTrans Prf.hyp0.eqSymm)
    · exact .botE _ (.impE hne.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))

/-- `|v − w|` for `v, w ∈ {0, 1}`: `0` if `v = w`, `1` otherwise. -/
private theorem dist_eq {v w : PTm n} (h : Γ ⊢[PRAAx] v ≐ w) : Γ ⊢[PRAAx] dist v w ≐ zero :=
  (congrAdd (congrMonus h (.eqRefl _)) (congrMonus (.eqRefl _) h)).eqTrans
    ((congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _))

private theorem dist_ne {v w : PTm n} (hv : Γ ⊢[PRAAx] (v ≐ zero) ⋎ (v ≐ one))
    (hw : Γ ⊢[PRAAx] (w ≐ zero) ⋎ (w ≐ one)) (hne : Γ ⊢[PRAAx] neg (v ≐ w)) :
    Γ ⊢[PRAAx] dist v w ≐ one := by
  refine .orE hv ?_ ?_
  · refine .orE hw.wk ?_ ?_
    · exact .botE _ (.impE hne.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))
    · refine (congrAdd (congrMonus Prf.hyp1 Prf.hyp0) (congrMonus Prf.hyp0 Prf.hyp1)).eqTrans ?_
      exact (congrAdd (zero_monus _) (monus_zero _)).eqTrans (zero_add _)
  · refine .orE hw.wk ?_ ?_
    · refine (congrAdd (congrMonus Prf.hyp1 Prf.hyp0) (congrMonus Prf.hyp0 Prf.hyp1)).eqTrans ?_
      exact (congrAdd (monus_zero _) (zero_monus _)).eqTrans (add_zero _)
    · exact .botE _ (.impE hne.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))

theorem parity_invariant₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] invFormula (f := f) := by
  ipra_ind [subst_ap1, subst_ap2]
  · refine (congrAp1 parF ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _))).eqTrans ?_
    exact par_par _
  · have ih : [invFormula (f := f)] ⊢[PRAAx] par (C f (var 0) + ℓ f zero) ≐ ℓ f (var 0) := Prf.hyp0
    -- C(N+1) + ℓ(0) = (C(N) + ℓ(0)) + |ℓ(N+1) − ℓ(N)|.
    have hs : [invFormula (f := f)] ⊢[PRAAx]
        C f (succ (var 0)) + ℓ f zero ≐ (C f (var 0) + ℓ f zero) + dist (ℓ f (succ (var 0))) (ℓ f (var 0)) := by
      refine (congrAdd (sum_succ' (changeBody f) (var 0) zero) (.eqRefl _)).eqTrans ?_
      simp only [inst2, changeBody, PTm.subst_add, PTm.subst_monus, subst_ap1,
        ConciseIPRA.PTm.subst_succ, Syn.subst_var, Matrix.cons_val_zero]
      exact add_right_comm _ _ _
    refine (congrAp1 parF hs).eqTrans ?_
    refine .orE (eq_or_ne (ℓ f (succ (var 0))) (ℓ f (var 0))) ?_ ?_
    · refine (congrAp1 parF ((congrAdd (.eqRefl _) (dist_eq Prf.hyp0)).eqTrans (add_zero _))).eqTrans ?_
      exact ih.wk.eqTrans Prf.hyp0.eqSymm
    · refine (congrAp1 parF ((congrAdd (.eqRefl _) (dist_ne (par_cases _) (par_cases _) Prf.hyp0)).eqTrans
        (succ_eq_add_one _).eqSymm)).eqTrans ?_
      refine flip ih.wk (par_cases _) (par_cases _) (.impI ?_)
      exact .impE Prf.hyp1 Prf.hyp0.eqSymm

/-- `par (C(N) + ℓ(0)) = ℓ(N)` for every `N`. -/
theorem parity_invariant : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (invFormula (f := f)) :=
  closeUniv 1 parity_invariant₀

/-- The one-dimensional Sperner lemma: `ℓ(0) = 0 → ℓ(N) = 1 → C(N)` is odd. -/
abbrev spernerFormula : Fm PTm 1 :=
  (ℓ f zero ≐ zero) ⟶ (ℓ f (var 0) ≐ one) ⟶ (par (C f (var 0)) ≐ one)

theorem sperner_1d : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (spernerFormula (f := f)) := by
  refine closeUniv 1 (.impI (.impI ?_))
  have h : ([ℓ f (var 0) ≐ one, ℓ f zero ≐ zero] : List (Fm PTm 1)) ⊢[PRAAx] invFormula (f := f) :=
    (parity_invariant₀ (f := f)).ofNil
  exact (congrAp1 parF ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) Prf.hyp1.eqSymm))).eqTrans
    (h.eqTrans Prf.hyp0)

end LeanProofs.IPRA.Topology.Sperner
