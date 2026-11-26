import IPRADerivations.Probability.Independence
import IPRADerivations.Core.Header

/-!
# A factor that depends only on the parameter leaves a double sum

A reusable rule for double sums `Independence.dsum a M N y = Σ_{i<M} Σ_{j<N} a(i, j, y)`, completing
`dsum_congr`, `dsum_add` (`Probability/Independence`) and `dsum_le` (`Probability/SymmetrizedMoments`).

For a one-variable term `k` and three-variable bodies `h`, `f` with `h(i, j, y) = k(y) · f(i, j, y)` at all terms:

  `Σ_{i<M} Σ_{j<N} h(i, j, y) = k(y) · Σ_{i<M} Σ_{j<N} f(i, j, y)`                           (`dsum_scale`).

The hypothesis is a pointwise identity for arbitrary terms in an arbitrary context, as in `dsum_congr`, so that it
applies under both summation binders; `at1 k y` is the value of `k` at `y`, and `shift_at1` moves it under a binder.
The proof is `Independence.sum_scale` on each row and then on the row sums.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DoubleSumScale

open_ipra
open LeanProofs.IPRA.Probability.Independence (row_pt sum_scale dsum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The value `k(y)` of a one-variable term. -/
abbrev at1 (k : PTm 1) (y : PTm n) : PTm n := Syn.subst ![y] k

theorem shift_at1 (k : PTm 1) (y : PTm n) : Syn.shift (at1 k y) = at1 k (Syn.shift y) := by
  simp only [at1, Syn.shift, Syn.subst_subst]
  congr 1; funext i; fin_cases i; rfl

/-- One row: `Σ_{j<N} h(i, j, y) = k(y) · Σ_{j<N} f(i, j, y)`. -/
theorem row_scale (h f : PTm 3) (k : PTm 1)
    (hp : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j y : PTm m), Δ ⊢[PRAAx] inst3 h i j y ≐ at1 k y * inst3 f i j y)
    (i N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB h)) N (pairT i y) ≐ at1 k y * ap2 (sumF (rowB f)) N (pairT i y) := by
  refine sum_scale (rowB h) (rowB f) N (at1 k y) (pairT i y) (pairT i y) (.allI (.impI ?_))
  rw [shift_pairT, shift_at1]
  exact (row_pt h _ _ _).eqTrans ((hp _ _ _).eqTrans (congrMul (.eqRefl _) (row_pt f _ _ _).eqSymm))

/-- `Σ_{i<M} Σ_{j<N} h(i, j, y) = k(y) · Σ_{i<M} Σ_{j<N} f(i, j, y)`. -/
theorem dsum_scale (h f : PTm 3) (k : PTm 1)
    (hp : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j y : PTm m), Δ ⊢[PRAAx] inst3 h i j y ≐ at1 k y * inst3 f i j y)
    (M N y : PTm n) : Γ ⊢[PRAAx] dsum h M N y ≐ at1 k y * dsum f M N y := by
  refine sum_scale (oB h) (oB f) M (at1 k y) (pairT N y) (pairT N y) (.allI (.impI ?_))
  rw [shift_pairT, shift_at1]
  exact (oB_at h _ _ _).eqTrans ((row_scale h f k hp _ _ _).eqTrans (congrMul (.eqRefl _) (oB_at f _ _ _).eqSymm))

end LeanProofs.IPRA.Foundations.DoubleSumScale
