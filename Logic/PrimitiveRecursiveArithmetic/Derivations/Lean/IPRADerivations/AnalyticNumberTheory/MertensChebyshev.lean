import IPRADerivations.AnalyticNumberTheory.MertensTotient
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.Core.CommonLemmas

/-!
# The Chebyshev identity for the Mertens function

Packet: `analytic-number-theory/mertens-ipra`, `identities.tex`, Theorem `thm:totient-chebyshev`, second
identity: `∑_{a=1}^{N} (log a) M(⌊N/a⌋) = ψ(N)`.

It is stated for every weight `w` in place of the logarithm: `Λ_w` is the weighted von Mangoldt function and
`L_w = Λ_w * 𝟏` the completely additive weight of `WeightedMangoldt` (`L_w(a) = log a` for `w = log`),
`ψ_w(x) = ∑_{1 ≤ n ≤ x} Λ_w(n)`, and `M = M⁺ − M⁻` with the negative part on the other side.

* `LamB`, `LwB`: `Λ_w` and `L_w` as bodies; `conv_lam`: `(Λ_w * 𝟏)(k) = L_w(k)` for `k ≥ 1`
  (`WeightedMangoldt.lambda_divsum`);
* `B_lam`, `sumRow`: the summatory function of `Λ_w * 𝟏` is that of `L_w`;
* **`chebyshev_floor`**: `∑_{d ≤ x} μ⁺(d) T_w(⌊x/d⌋) = ψ_w(x) + ∑_{d ≤ x} μ⁻(d) T_w(⌊x/d⌋)` with
  `T_w(m) = ∑_{1 ≤ k ≤ m} L_w(k)` (`= L_w(m!)`): the summed inversion `MobiusSummatory.mobius_summatory` at
  `g = Λ_w`, i.e. `ψ(x) = ∑_d μ(d) log(⌊x/d⌋!)`;
* **`chebyshev_mertens`**: `∑_{a ≤ x} L_w(a) M⁺(⌊x/a⌋) = ψ_w(x) + ∑_{a ≤ x} L_w(a) M⁻(⌊x/a⌋)`, by the
  exchange `HyperbolaSwap.hyp_swap`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MertensChebyshev

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at Bs bS inst2_bS)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (bF gS mobius_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap (hyp_swap)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor (inst2_oneB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (lamB Lam ellB Lw DB lambda_divsum)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (DB_at)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Weight

variable (w : PTm 2)

/-- `Λ_w(d)`, over `0 = d`, `1 = y`. -/
abbrev LamB : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (var 1))

theorem inst2_LamB (d y : PTm n) : inst2 (LamB w) d y = Lam w d y := by simp [inst2, subst_ap2]

/-- `L_w(k)`, over `0 = k`, `1 = y`. -/
abbrev LwB : PTm 2 := ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) (var 1))

theorem inst2_LwB (k y : PTm n) : inst2 (LwB w) k y = Lw w k y := by simp [inst2, subst_ap2]

alias mul_one_r := Common.mul_one_right

/-- `(Λ_w * 𝟏)(k) = L_w(k)` for `k ≥ 1`. -/
theorem conv_lam {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (y : PTm n) :
    Γ ⊢[PRAAx] conv (LamB w) one k y ≐ Lw w k y := by
  refine .eqTrans ?_ (lambda_divsum w hk)
  refine sum_congr_bounded (cvB (LamB w) one) (DB w) (pairT k y) (pairT k y) (succ k) (.allI (.impI ?_))
  rw [shift_pairT]
  refine (cv_at (LamB w) one _ _ _).eqTrans (.eqTrans ?_ (DB_at w _ _ _).eqSymm)
  rw [inst2_LamB, inst2_oneB]
  exact congrMul (.eqRefl _) (mul_one_r _)

/-- `∑_{k < m} (Λ_w * 𝟏)(k + 1) = ∑_{k < m} L_w(k + 1)`. -/
theorem B_lam (m y : PTm n) : Γ ⊢[PRAAx] Bs (bF (LamB w)) m y ≐ Bs (LwB w) m y := by
  refine sum_congr_bounded (bS (bF (LamB w))) (bS (LwB w)) y y m (.allI (.impI ?_))
  rw [inst2_bS, inst2_bS, inst2_cvF, inst2_LwB]
  exact conv_lam w (congrSucc (pred_succ _).eqSymm) _

theorem row (a : PTm 2) (d x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB a (bF (LamB w))) d (pairT x y) ≐ inst2 (RB a (LwB w)) d (pairT x y) :=
  (RB_at a (bF (LamB w)) d x y).eqTrans
    ((congrMul (.eqRefl _) (B_lam w _ _)).eqTrans (RB_at a (LwB w) d x y).eqSymm)

theorem sumRow (a : PTm 2) (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB a (bF (LamB w)))) (succ x) (pairT x y) ≐
      ap2 (sumF (RB a (LwB w))) (succ x) (pairT x y) :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (by rw [shift_pairT]; exact row w _ _ _ _)))

/-- **The Chebyshev identity, floor form**:
`∑_{d ≤ x} μ⁺(d) T_w(⌊x/d⌋) = ψ_w(x) + ∑_{d ≤ x} μ⁻(d) T_w(⌊x/d⌋)`, `T_w(m) = ∑_{1 ≤ k ≤ m} L_w(k)`. -/
theorem chebyshev_floor (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aPB (LwB w))) (succ x) (pairT x y) ≐
      ap2 (sumF (gS (LamB w))) (succ x) y + ap2 (sumF (RB aNB (LwB w))) (succ x) (pairT x y) :=
  (sumRow w aPB x y).eqSymm.eqTrans
    ((mobius_summatory (LamB w) x y).eqTrans (congrAdd (.eqRefl _) (sumRow w aNB x y)))

/-- **The Chebyshev identity for the Mertens function**:
`∑_{a ≤ x} L_w(a) M⁺(⌊x/a⌋) = ψ_w(x) + ∑_{a ≤ x} L_w(a) M⁻(⌊x/a⌋)`. -/
theorem chebyshev_mertens (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB (LwB w) aPB)) (succ x) (pairT x y) ≐
      ap2 (sumF (gS (LamB w))) (succ x) y + ap2 (sumF (RB (LwB w) aNB)) (succ x) (pairT x y) :=
  (hyp_swap (LwB w) aPB x y).eqTrans
    ((chebyshev_floor w x y).eqTrans (congrAdd (.eqRefl _) (hyp_swap aNB (LwB w) x y)))

/-- The terms of `chebyshev_mertens`: `[a ≥ 1] L_w(a) · ∑_{k < ⌊x/a⌋} b(k + 1)`. -/
theorem mertens_term (b : PTm 2) (a x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB (LwB w) b) a (pairT x y) ≐ (sg a * Lw w a y) * Bs b (quo x a) y := by
  have h := RB_at (Γ := Γ) (LwB w) b a x y
  rw [inst2_LwB] at h
  exact h

end Weight

end LeanProofs.IPRA.AnalyticNumberTheory.MertensChebyshev
