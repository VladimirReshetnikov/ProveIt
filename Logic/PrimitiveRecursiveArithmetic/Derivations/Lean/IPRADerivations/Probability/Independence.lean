import IPRADerivations.Probability.Lotus

/-!
# Product laws and independence

Packet: `probability/expected_value_ipra_2026-11-16`, Section 7 (`def:product-law`,
`thm:ind-product`, `cor:ind-var-sum`). Two finite laws with weight bodies `w(i, x)` on `i < M` and
`v(j, x)` on `j < N` have the product law with weight `w_i v_j` on pairs `(i, j)`. Every statement is
cleared of the total weight `T = W V`, so no division occurs.

Reusable double-sum tools (`dsum a M N x = ∑_{i<M} ∑_{j<N} a(i, j, x)`):

* `sum_scale`: `h(j) = K f(j)` for `j < N` gives `∑_{j<N} h(j) = K ∑_{j<N} f(j)`;
* `dsum_rows`: a double sum is the sum of its evaluated row sums;
* `dsum_congr`, `dsum_add`: pointwise congruence and additivity;
* `sum_mul_sum`: `∑_{i<M} ∑_{j<N} f(i) g(j) = (∑_{i<M} f(i)) (∑_{j<N} g(j))`.

The product law:

* `product_total` (`def:product-law`): `∑∑ w_i v_j = W V`;
* `ind_product` (`thm:ind-product`): `∑∑ w_i v_j X_i Y_j = Ew(X) · Ev(Y)`;
* `ind_cov_zero`: `T · ∑∑ w v X Y = (∑∑ w v X)(∑∑ w v Y)`, i.e. the covariance vanishes;
* `ind_sum_first`, `ind_sum_second`: the first and second moments of `X_i + Y_j`;
* `ind_var_sum` (`cor:ind-var-sum`): `T Q_Z − S_Z² = V² (W Q_X − S_X²) + W² (V Q_Y − S_Y²)` for
  `Z = X + Y`, with the subtracted terms moved to the other side.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Independence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Shifts and pointwise evaluations -/

theorem shift_inst2 (f : PTm 2) (i x : PTm n) :
    Syn.shift (inst2 f i x) = inst2 f (Syn.shift i) (Syn.shift x) := by
  simp only [Syn.shift, subst_inst2]

theorem shift_sum (f : PTm 2) (N x : PTm n) :
    Syn.shift (ap2 (sumF f) N x) = ap2 (sumF f) (Syn.shift N) (Syn.shift x) := by
  simp only [Syn.shift, subst_ap2]

theorem row_pt (a : PTm 3) (i j x : PTm n) : Γ ⊢[PRAAx] inst2 (rowB a) j (pairT i x) ≐ inst3 a i j x := by
  rw [inst2_rowB]
  exact congrInst3 a (fst_pair _ _) (.eqRefl _) (snd_pair _ _)

theorem col_pt (a : PTm 3) (i j x : PTm n) : Γ ⊢[PRAAx] inst2 (colB a) i (pairT j x) ≐ inst3 a i j x := by
  rw [inst2_colB]
  exact congrInst3 a (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem cm_pt (f : PTm 2) (j K x : PTm n) : Γ ⊢[PRAAx] inst2 (cmB f) j (pairT K x) ≐ K * inst2 f j x := by
  rw [inst2_cmB]
  exact congrMul (fst_pair _ _) (congrInst2 f (.eqRefl _) (snd_pair _ _))

theorem inst3_mul' (a b : PTm 3) (i j x : PTm n) : inst3 (a * b) i j x = inst3 a i j x * inst3 b i j x := by
  simp [inst3]

theorem inst3_add' (a b : PTm 3) (i j x : PTm n) : inst3 (a + b) i j x = inst3 a i j x + inst3 b i j x := by
  simp [inst3]

/-! ## Scaling a sum -/

/-- If `h(j, y) = K · f(j, x)` for `j < N`, then `∑_{j<N} h(j, y) = K · ∑_{j<N} f(j, x)`. -/
theorem sum_scale (h f : PTm 2) (N K x y : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 h (var 0) (Syn.shift y) ≐ Syn.shift K * inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF h) N y ≐ K * ap2 (sumF f) N x := by
  refine (sum_congr_bounded h (cmB f) y (pairT K x) N (.allI (.impI ?_))).eqTrans (sum_const_mul f N K x)
  rw [shift_pairT]
  exact (Prf.impE hp.allOpen.wk Prf.hyp0).eqTrans (cm_pt f _ _ _).eqSymm

/-! ## Double sums -/

/-- `∑_{i<M} ∑_{j<N} a(i, j, x)`. -/
abbrev dsum (a : PTm 3) (M N x : PTm n) : PTm n := ap2 (sumF (oB a)) M (pairT N x)

/-- A double sum is the sum of its row sums, once each row `i < M` is evaluated as `r(i, y)`. -/
theorem dsum_rows (a : PTm 3) (r : PTm 2) (M N x y : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (ap2 (sumF (rowB a)) (Syn.shift N) (pairT (var 0) (Syn.shift x)) ≐ inst2 r (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] dsum a M N x ≐ ap2 (sumF r) M y := by
  refine sum_congr_bounded (oB a) r (pairT N x) y M (.allI (.impI ?_))
  rw [shift_pairT]
  exact (oB_at a _ _ _).eqTrans (Prf.impE h.allOpen.wk Prf.hyp0)

/-- Pointwise equal bodies have equal double sums. -/
theorem dsum_congr (a b : PTm 3)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j x : PTm m), Δ ⊢[PRAAx] inst3 a i j x ≐ inst3 b i j x)
    (M N x : PTm n) : Γ ⊢[PRAAx] dsum a M N x ≐ dsum b M N x := by
  refine sum_congr_bounded (oB a) (oB b) (pairT N x) (pairT N x) M (.allI (.impI ?_))
  rw [inst2_oB, inst2_oB]
  refine sum_congr_bounded (rowB a) (rowB b) _ _ _ (.allI (.impI ?_))
  rw [inst2_rowB, inst2_rowB]
  exact h _ _ _

/-- `∑∑ (a + b) = ∑∑ a + ∑∑ b`. -/
theorem dsum_add (a b : PTm 3) (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (a + b) M N x ≐ dsum a M N x + dsum b M N x := by
  refine (sum_congr_bounded (oB (a + b)) (addBody (oB a) (oB b)) (pairT N x) (pairT N x) M
    (.allI (.impI ?_))).eqTrans (sum_add (oB a) (oB b) M (pairT N x))
  rw [inst2_addBody, inst2_oB, inst2_oB, inst2_oB]
  refine (sum_congr_bounded (rowB (a + b)) (addBody (rowB a) (rowB b)) _ _ _ (.allI (.impI ?_))).eqTrans
    (sum_add (rowB a) (rowB b) _ _)
  rw [inst2_addBody, inst2_rowB, inst2_rowB, inst2_rowB, inst3_add']
  exact .eqRefl _

/-! ## Products of sums -/

/-- `f(i, x) · g(j, x)`. -/
def pmB (f g : PTm 2) : PTm 3 := Syn.subst ![var 0, var 2] f * Syn.subst ![var 1, var 2] g

theorem inst3_pmB (f g : PTm 2) (i j x : PTm n) : inst3 (pmB f g) i j x = inst2 f i x * inst2 g j x := by
  simp only [inst3, pmB, inst2, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · congr 1; funext k; fin_cases k <;> rfl
  · congr 1; funext k; fin_cases k <;> rfl

/-- A row of the product: `∑_{j<N} f(i) g(j) = f(i) · ∑_{j<N} g(j)`. -/
theorem pm_row (f g : PTm 2) (i N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (pmB f g))) N (pairT i x) ≐ inst2 f i x * ap2 (sumF g) N x := by
  refine sum_scale (rowB (pmB f g)) g N (inst2 f i x) x (pairT i x) (.allI (.impI ?_))
  rw [shift_pairT, shift_inst2]
  refine (row_pt _ _ _ _).eqTrans ?_
  rw [inst3_pmB]
  exact .eqRefl _

/-- `∑_{i<M} ∑_{j<N} f(i) g(j) = (∑_{i<M} f(i)) · (∑_{j<N} g(j))`. -/
theorem sum_mul_sum (f g : PTm 2) (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB f g) M N x ≐ ap2 (sumF f) M x * ap2 (sumF g) N x := by
  have e : Γ ⊢[PRAAx] dsum (pmB f g) M N x ≐ ap2 (sumF (cmB f)) M (pairT (ap2 (sumF g) N x) x) := by
    refine dsum_rows (pmB f g) (cmB f) M N x (pairT (ap2 (sumF g) N x) x) (.allI (.impI ?_))
    rw [shift_pairT, shift_sum]
    exact (pm_row f g _ _ _).eqTrans ((mul_comm _ _).eqTrans (cm_pt f _ _ _).eqSymm)
  exact e.eqTrans ((sum_const_mul f M _ x).eqTrans (mul_comm _ _))

/-! ## The product law -/

section Product

variable (w X v Y : PTm 2)

/-- `def:product-law`: the product law has total weight `W · V`. -/
theorem product_total (M N x : PTm n) : Γ ⊢[PRAAx] dsum (pmB w v) M N x ≐ Wt w M x * Wt v N x :=
  sum_mul_sum w v M N x

/-- `thm:ind-product`: `∑∑ (w_i v_j) (X_i Y_j) = Ew(X) · Ev(Y)`. -/
theorem ind_product (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB w v * pmB X Y) M N x ≐ Ew w X M x * Ew v Y N x := by
  refine (dsum_congr (pmB w v * pmB X Y) (pmB (w * X) (v * Y)) (fun i j x => ?_) M N x).eqTrans
    (sum_mul_sum (w * X) (v * Y) M N x)
  rw [inst3_mul', inst3_pmB, inst3_pmB, inst3_pmB, inst2_mul', inst2_mul']
  ipra_ring

/-- The covariance vanishes on the product law:
`T · ∑∑ w v X Y = (∑∑ w v X) · (∑∑ w v Y)`, with `T = ∑∑ w v`. -/
theorem ind_cov_zero (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB w v) M N x * dsum (pmB w v * pmB X Y) M N x ≐
      dsum (pmB (w * X) v) M N x * dsum (pmB w (v * Y)) M N x := by
  have r : Γ ⊢[PRAAx] (Wt w M x * Wt v N x) * (Ew w X M x * Ew v Y N x) ≐
      (Ew w X M x * Wt v N x) * (Wt w M x * Ew v Y N x) := by
    ipra_ring
  exact (congrMul (product_total w v M N x) (ind_product w X v Y M N x)).eqTrans
    (r.eqTrans (congrMul (sum_mul_sum (w * X) v M N x) (sum_mul_sum w (v * Y) M N x)).eqSymm)

/-- `X(i, x) + Y(j, x)`. -/
def spB : PTm 3 := Syn.subst ![var 0, var 2] X + Syn.subst ![var 1, var 2] Y

theorem inst3_spB (i j x : PTm n) : inst3 (spB X Y) i j x = inst2 X i x + inst2 Y j x := by
  simp only [inst3, spB, inst2, PTm.subst_add, Syn.subst_subst]
  congr 1
  · congr 1; funext k; fin_cases k <;> rfl
  · congr 1; funext k; fin_cases k <;> rfl

/-- The first moment of `Z = X + Y` on the product law: `S_Z = Ew(X) · V + W · Ev(Y)`. -/
theorem ind_sum_first (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB w v * spB X Y) M N x ≐ Ew w X M x * Wt v N x + Wt w M x * Ew v Y N x := by
  refine (dsum_congr (pmB w v * spB X Y) (pmB (w * X) v + pmB w (v * Y)) (fun i j x => ?_) M N x).eqTrans
    ((dsum_add _ _ M N x).eqTrans (congrAdd (sum_mul_sum (w * X) v M N x) (sum_mul_sum w (v * Y) M N x)))
  rw [inst3_mul', inst3_add', inst3_pmB, inst3_pmB, inst3_pmB, inst3_spB, inst2_mul', inst2_mul']
  ipra_ring

/-- The second moment of `Z = X + Y` on the product law:
`Q_Z = Ew(X²) · V + 2 Ew(X) Ev(Y) + W · Ev(Y²)`. -/
theorem ind_sum_second (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB w v * (spB X Y * spB X Y)) M N x ≐
      Ew w (X * X) M x * Wt v N x + (Ew w X M x * Ew v Y N x + Ew w X M x * Ew v Y N x) +
        Wt w M x * Ew v (Y * Y) N x := by
  refine (dsum_congr (pmB w v * (spB X Y * spB X Y))
    (pmB (w * (X * X)) v + (pmB (w * X) (v * Y) + pmB (w * X) (v * Y)) + pmB w (v * (Y * Y)))
    (fun i j x => ?_) M N x).eqTrans
    ((dsum_add _ _ M N x).eqTrans (congrAdd ((dsum_add _ _ M N x).eqTrans
      (congrAdd (sum_mul_sum (w * (X * X)) v M N x)
        ((dsum_add _ _ M N x).eqTrans
          (congrAdd (sum_mul_sum (w * X) (v * Y) M N x) (sum_mul_sum (w * X) (v * Y) M N x)))))
      (sum_mul_sum w (v * (Y * Y)) M N x)))
  rw [inst3_mul', inst3_mul', inst3_add', inst3_add', inst3_add', inst3_pmB, inst3_pmB, inst3_pmB, inst3_pmB,
    inst3_spB, inst2_mul', inst2_mul', inst2_mul', inst2_mul', inst2_mul', inst2_mul']
  ipra_ring

/-- `cor:ind-var-sum`: for `Z = X + Y` on the product law, with `T = ∑∑ w v`,
`T Q_Z − S_Z² = V² (W Q_X − S_X²) + W² (V Q_Y − S_Y²)`, i.e. `Var(X + Y) = Var(X) + Var(Y)`.
The subtracted terms are moved to the other side. -/
theorem ind_var_sum (M N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB w v) M N x * dsum (pmB w v * (spB X Y * spB X Y)) M N x +
        Wt v N x * Wt v N x * (Ew w X M x * Ew w X M x) + Wt w M x * Wt w M x * (Ew v Y N x * Ew v Y N x) ≐
      dsum (pmB w v * spB X Y) M N x * dsum (pmB w v * spB X Y) M N x +
        Wt v N x * Wt v N x * (Wt w M x * Ew w (X * X) M x) +
        Wt w M x * Wt w M x * (Wt v N x * Ew v (Y * Y) N x) := by
  have hT := product_total (Γ := Γ) w v M N x
  have hS := ind_sum_first (Γ := Γ) w X v Y M N x
  have hQ := ind_sum_second (Γ := Γ) w X v Y M N x
  have r : Γ ⊢[PRAAx] (Wt w M x * Wt v N x) *
        (Ew w (X * X) M x * Wt v N x + (Ew w X M x * Ew v Y N x + Ew w X M x * Ew v Y N x) +
          Wt w M x * Ew v (Y * Y) N x) +
        Wt v N x * Wt v N x * (Ew w X M x * Ew w X M x) + Wt w M x * Wt w M x * (Ew v Y N x * Ew v Y N x) ≐
      (Ew w X M x * Wt v N x + Wt w M x * Ew v Y N x) * (Ew w X M x * Wt v N x + Wt w M x * Ew v Y N x) +
        Wt v N x * Wt v N x * (Wt w M x * Ew w (X * X) M x) +
        Wt w M x * Wt w M x * (Wt v N x * Ew v (Y * Y) N x) := by
    ipra_ring
  exact (congrAdd (congrAdd (congrMul hT hQ) (.eqRefl _)) (.eqRefl _)).eqTrans
    (r.eqTrans (congrAdd (congrAdd (congrMul hS hS) (.eqRefl _)) (.eqRefl _)).eqSymm)

end Product

end LeanProofs.IPRA.Probability.Independence
