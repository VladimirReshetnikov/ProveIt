import IPRADerivations.AnalyticNumberTheory.ConvSummatory
import IPRADerivations.AnalyticNumberTheory.DivisorSwapP
import IPRADerivations.AnalyticNumberTheory.SymmetryInstances
import IPRADerivations.Core.Header

/-!
# The hyperbola swap of two summatory functions (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`. The block sums of the
discrete contraction run over divisors `d` with `x/d` in a block; their signed mean (`con:signed`) is controlled by
exchanging the order of summation,

  `Σ_{1≤d≤x} a(d) B(⌊x/d⌋) = Σ_{n≤x} (a * b)(n) = Σ_{n≤x} (b * a)(n) = Σ_{1≤n≤x} b(n) A(⌊x/n⌋)`,

with `A`, `B` the summatory functions of `a`, `b` (`ConvSummatory.conv_summatory` twice and
`DivisorSwapP.conv_comm`; the term `n = 0` vanishes on both sides by `SymmetryInstances.conv_zero`):

* `conv_congr_m`: congruence of `(f * g)(m, y)` in `m`;
* `conv_comm0`: `(f * g)(m) = (g * f)(m)` for every `m`, including `m = 0`;
* `hyp_swap`: the swap, for bodies with a common parameter `y`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB conv_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP (conv_comm)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (conv_zero)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem conv_congr_m (f g : PTm 2) {m m' : PTm n} (y : PTm n) (h : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] conv f g m y ≐ conv f g m' y :=
  congrAp2 (sumF (cvB f g)) (congrSucc h) (congrPairT h (.eqRefl y))

/-- `(f * g)(m) = (g * f)(m)`, also at `m = 0`. -/
theorem conv_comm0 (f g : PTm 2) (m y : PTm n) : Γ ⊢[PRAAx] conv f g m y ≐ conv g f m y := by
  refine .orE (zero_or_succ m) ?_ ?_
  · exact (conv_congr_m f g y Prf.hyp0).eqTrans ((conv_zero f g y).eqTrans
      ((conv_zero g f y).eqSymm.eqTrans (conv_congr_m g f y Prf.hyp0).eqSymm))
  · exact conv_comm f g Prf.hyp0

/-- `Σ_{1≤d≤x} a(d) B(⌊x/d⌋) = Σ_{1≤n≤x} b(n) A(⌊x/n⌋)`. -/
theorem hyp_swap (a b : PTm 2) (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB a b)) (succ x) (pairT x y) ≐ ap2 (sumF (RB b a)) (succ x) (pairT x y) := by
  refine (conv_summatory a b x y).eqSymm.eqTrans (.eqTrans ?_ (conv_summatory b a x y))
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cvF, inst2_cvF]
  exact conv_comm0 _ _ _ _

end LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap
