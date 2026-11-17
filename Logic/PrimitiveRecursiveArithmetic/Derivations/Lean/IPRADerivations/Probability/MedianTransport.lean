import IPRADerivations.Probability.MedianSymmetry

/-!
# Monotone transport of balance medians

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:monotone`. For a sample
`x(i, p)` of length `N`, a threshold `t` and a map `f(y, p)`, write `f x` for the sample
`f(x_i, p)` (`Permutation.FS f x`). Strict monotonicity is used only on the pairs `(x_i, t)`, so it
is assumed in that bounded form (`incAll`, `decAll`), which any strictly monotone `f` satisfies:

* `inc_below`, `inc_above`: for increasing `f`, `[f x < f t] = [x < t]` and `[f t < f x] = [t < x]`;
* `inc_counts`, `inc_median` (`thm:monotone`): `B_{f x}(f t) = B_x(t)`, `A_{f x}(f t) = A_x(t)`,
  so `t` is a balance median of `x` iff `f t` is one of `f x`;
* `dec_counts`, `dec_median`: for decreasing `f` the two counts are exchanged,
  `B_{f x}(f t) = A_x(t)` and `A_{f x}(f t) = B_x(t)`, and the conclusion is the same.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Probability.MedianCounts
open LeanProofs.IPRA.Probability.MedianSymmetry (shift_pairT')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Map

variable (F : PTm 2)

/-! ## Pointwise -/

theorem eqc_ft_fx {x t p : PTm n} (h : Γ ⊢[PRAAx] t ≐ x) :
    Γ ⊢[PRAAx] sg (monus (inst2 F t p) (inst2 F x p)) ≐ zero :=
  sg_le (le_congr (.eqRefl _) (congrInst2 F h (.eqRefl p)) (le_refl _))

theorem eqc_fx_ft {x t p : PTm n} (h : Γ ⊢[PRAAx] t ≐ x) :
    Γ ⊢[PRAAx] sg (monus (inst2 F x p) (inst2 F t p)) ≐ zero :=
  sg_le (le_congr (congrInst2 F h (.eqRefl p)) (.eqRefl _) (le_refl _))

theorem eqc_t_x {x t : PTm n} (h : Γ ⊢[PRAAx] t ≐ x) : Γ ⊢[PRAAx] sg (monus t x) ≐ zero :=
  sg_le (le_congr (.eqRefl _) h (le_refl t))

theorem eqc_x_t {x t : PTm n} (h : Γ ⊢[PRAAx] t ≐ x) : Γ ⊢[PRAAx] sg (monus x t) ≐ zero :=
  sg_le (le_congr h (.eqRefl _) (le_refl t))

/-- For increasing `f`: `[f x < f t] = [x < t]`. -/
theorem inc_below {x t p : PTm n} (h₁ : Γ ⊢[PRAAx] lt x t ⟶ lt (inst2 F x p) (inst2 F t p))
    (h₂ : Γ ⊢[PRAAx] lt t x ⟶ lt (inst2 F t p) (inst2 F x p)) :
    Γ ⊢[PRAAx] sg (monus (inst2 F t p) (inst2 F x p)) ≐ sg (monus t x) := by
  refine .orE (lt_or_le x t) ((sg_lt (.impE h₁.wk Prf.hyp0)).eqTrans (sg_lt Prf.hyp0).eqSymm)
    (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact (sg_le (le_of_lt (.impE h₂.wk.wk Prf.hyp0))).eqTrans (sg_le (le_of_lt Prf.hyp0)).eqSymm
  · exact (eqc_ft_fx F Prf.hyp0).eqTrans (eqc_t_x Prf.hyp0).eqSymm

/-- For increasing `f`: `[f t < f x] = [t < x]`. -/
theorem inc_above {x t p : PTm n} (h₁ : Γ ⊢[PRAAx] lt x t ⟶ lt (inst2 F x p) (inst2 F t p))
    (h₂ : Γ ⊢[PRAAx] lt t x ⟶ lt (inst2 F t p) (inst2 F x p)) :
    Γ ⊢[PRAAx] sg (monus (inst2 F x p) (inst2 F t p)) ≐ sg (monus x t) := by
  refine .orE (lt_or_le x t) ((sg_le (le_of_lt (.impE h₁.wk Prf.hyp0))).eqTrans (sg_le (le_of_lt Prf.hyp0)).eqSymm)
    (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact (sg_lt (.impE h₂.wk.wk Prf.hyp0)).eqTrans (sg_lt Prf.hyp0).eqSymm
  · exact (eqc_fx_ft F Prf.hyp0).eqTrans (eqc_x_t Prf.hyp0).eqSymm

/-- For decreasing `f`: `[f x < f t] = [t < x]`. -/
theorem dec_below {x t p : PTm n} (h₁ : Γ ⊢[PRAAx] lt x t ⟶ lt (inst2 F t p) (inst2 F x p))
    (h₂ : Γ ⊢[PRAAx] lt t x ⟶ lt (inst2 F x p) (inst2 F t p)) :
    Γ ⊢[PRAAx] sg (monus (inst2 F t p) (inst2 F x p)) ≐ sg (monus x t) := by
  refine .orE (lt_or_le x t) ((sg_le (le_of_lt (.impE h₁.wk Prf.hyp0))).eqTrans (sg_le (le_of_lt Prf.hyp0)).eqSymm)
    (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact (sg_lt (.impE h₂.wk.wk Prf.hyp0)).eqTrans (sg_lt Prf.hyp0).eqSymm
  · exact (eqc_ft_fx F Prf.hyp0).eqTrans (eqc_x_t Prf.hyp0).eqSymm

/-- For decreasing `f`: `[f t < f x] = [x < t]`. -/
theorem dec_above {x t p : PTm n} (h₁ : Γ ⊢[PRAAx] lt x t ⟶ lt (inst2 F t p) (inst2 F x p))
    (h₂ : Γ ⊢[PRAAx] lt t x ⟶ lt (inst2 F x p) (inst2 F t p)) :
    Γ ⊢[PRAAx] sg (monus (inst2 F x p) (inst2 F t p)) ≐ sg (monus t x) := by
  refine .orE (lt_or_le x t) ((sg_lt (.impE h₁.wk Prf.hyp0)).eqTrans (sg_lt Prf.hyp0).eqSymm)
    (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact (sg_le (le_of_lt (.impE h₂.wk.wk Prf.hyp0))).eqTrans (sg_le (le_of_lt Prf.hyp0)).eqSymm
  · exact (eqc_fx_ft F Prf.hyp0).eqTrans (eqc_t_x Prf.hyp0).eqSymm

/-! ## Counts -/

variable (X : PTm 2)

/-- `f` is strictly increasing on the pairs `(x_i, t)`, `i < N`. -/
abbrev incAll (N t p : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    ((lt (inst2 X (var 0) (Syn.shift p)) (Syn.shift t) ⟶
        lt (inst2 F (inst2 X (var 0) (Syn.shift p)) (Syn.shift p)) (inst2 F (Syn.shift t) (Syn.shift p))) ⋏
      (lt (Syn.shift t) (inst2 X (var 0) (Syn.shift p)) ⟶
        lt (inst2 F (Syn.shift t) (Syn.shift p)) (inst2 F (inst2 X (var 0) (Syn.shift p)) (Syn.shift p)))))

/-- `f` is strictly decreasing on the pairs `(x_i, t)`, `i < N`. -/
abbrev decAll (N t p : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    ((lt (inst2 X (var 0) (Syn.shift p)) (Syn.shift t) ⟶
        lt (inst2 F (Syn.shift t) (Syn.shift p)) (inst2 F (inst2 X (var 0) (Syn.shift p)) (Syn.shift p))) ⋏
      (lt (Syn.shift t) (inst2 X (var 0) (Syn.shift p)) ⟶
        lt (inst2 F (inst2 X (var 0) (Syn.shift p)) (Syn.shift p)) (inst2 F (Syn.shift t) (Syn.shift p)))))

theorem shift_inst2 (t p : PTm n) : Syn.shift (inst2 F t p) = inst2 F (Syn.shift t) (Syn.shift p) := by
  simp only [Syn.shift, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

/-- `thm:monotone`, increasing: `B_{f x}(f t) = B_x(t)` and `A_{f x}(f t) = A_x(t)`. -/
theorem inc_counts {N t p : PTm n} (hf : Γ ⊢[PRAAx] incAll F X N t p) :
    Γ ⊢[PRAAx] Bc (Permutation.FS F X) N (inst2 F t p) p ≐ Bc X N t p ⋏
      Ac (Permutation.FS F X) N (inst2 F t p) p ≐ Ac X N t p := by
  refine .andI (sum_congr_bounded _ _ _ _ N (.allI (.impI ?_))) (sum_congr_bounded _ _ _ _ N (.allI (.impI ?_)))
  · have h := Prf.impE hf.allOpen.wk Prf.hyp0
    rw [shift_pairT', shift_pairT', shift_inst2]
    refine (below_pt _ _ _ _).eqTrans (.eqTrans ?_ (below_pt _ _ _ _).eqSymm)
    rw [Permutation.inst2_FS]
    exact inc_below F (Prf.andE₁ h) (Prf.andE₂ h)
  · have h := Prf.impE hf.allOpen.wk Prf.hyp0
    rw [shift_pairT', shift_pairT', shift_inst2]
    refine (above_pt _ _ _ _).eqTrans (.eqTrans ?_ (above_pt _ _ _ _).eqSymm)
    rw [Permutation.inst2_FS]
    exact inc_above F (Prf.andE₁ h) (Prf.andE₂ h)

/-- `thm:monotone`, decreasing: `B_{f x}(f t) = A_x(t)` and `A_{f x}(f t) = B_x(t)`. -/
theorem dec_counts {N t p : PTm n} (hf : Γ ⊢[PRAAx] decAll F X N t p) :
    Γ ⊢[PRAAx] Bc (Permutation.FS F X) N (inst2 F t p) p ≐ Ac X N t p ⋏
      Ac (Permutation.FS F X) N (inst2 F t p) p ≐ Bc X N t p := by
  refine .andI (sum_congr_bounded _ _ _ _ N (.allI (.impI ?_))) (sum_congr_bounded _ _ _ _ N (.allI (.impI ?_)))
  · have h := Prf.impE hf.allOpen.wk Prf.hyp0
    rw [shift_pairT', shift_pairT', shift_inst2]
    refine (below_pt _ _ _ _).eqTrans (.eqTrans ?_ (above_pt _ _ _ _).eqSymm)
    rw [Permutation.inst2_FS]
    exact dec_below F (Prf.andE₁ h) (Prf.andE₂ h)
  · have h := Prf.impE hf.allOpen.wk Prf.hyp0
    rw [shift_pairT', shift_pairT', shift_inst2]
    refine (above_pt _ _ _ _).eqTrans (.eqTrans ?_ (below_pt _ _ _ _).eqSymm)
    rw [Permutation.inst2_FS]
    exact dec_above F (Prf.andE₁ h) (Prf.andE₂ h)

theorem congrIsMed {X' : PTm 2} {N t t' p : PTm n}
    (hB : Γ ⊢[PRAAx] Bc X' N t' p ≐ Bc X N t p) (hA : Γ ⊢[PRAAx] Ac X' N t' p ≐ Ac X N t p) :
    Γ ⊢[PRAAx] isMed X N t p ⟶ isMed X' N t' p :=
  .impI (.andI (le_congr (congrMul (.eqRefl _) hB.wk.eqSymm) (.eqRefl _) (Prf.andE₁ Prf.hyp0))
    (le_congr (congrMul (.eqRefl _) hA.wk.eqSymm) (.eqRefl _) (Prf.andE₂ Prf.hyp0)))

/-- `thm:monotone`, increasing: `t ∈ Med(x)` iff `f t ∈ Med(f x)`. -/
theorem inc_median {N t p : PTm n} (hf : Γ ⊢[PRAAx] incAll F X N t p) :
    Γ ⊢[PRAAx] (isMed X N t p ⟶ isMed (Permutation.FS F X) N (inst2 F t p) p) ⋏
      (isMed (Permutation.FS F X) N (inst2 F t p) p ⟶ isMed X N t p) := by
  have c := inc_counts F X hf
  exact .andI (congrIsMed X (Prf.andE₁ c) (Prf.andE₂ c))
    (congrIsMed (Permutation.FS F X) (Prf.andE₁ c).eqSymm (Prf.andE₂ c).eqSymm)

/-- `thm:monotone`, decreasing: `t ∈ Med(x)` iff `f t ∈ Med(f x)`, with the counts exchanged. -/
theorem dec_median {N t p : PTm n} (hf : Γ ⊢[PRAAx] decAll F X N t p) :
    Γ ⊢[PRAAx] (isMed X N t p ⟶ isMed (Permutation.FS F X) N (inst2 F t p) p) ⋏
      (isMed (Permutation.FS F X) N (inst2 F t p) p ⟶ isMed X N t p) := by
  have c := dec_counts F X hf
  refine .andI (.impI (.andI ?_ ?_)) (.impI (.andI ?_ ?_))
  · exact le_congr (congrMul (.eqRefl _) (Prf.andE₁ c).wk.eqSymm) (.eqRefl _) (Prf.andE₂ Prf.hyp0)
  · exact le_congr (congrMul (.eqRefl _) (Prf.andE₂ c).wk.eqSymm) (.eqRefl _) (Prf.andE₁ Prf.hyp0)
  · exact le_congr (congrMul (.eqRefl _) (Prf.andE₂ c).wk) (.eqRefl _) (Prf.andE₂ Prf.hyp0)
  · exact le_congr (congrMul (.eqRefl _) (Prf.andE₁ c).wk) (.eqRefl _) (Prf.andE₁ Prf.hyp0)

end Map

end LeanProofs.IPRA.Probability.MedianTransport
