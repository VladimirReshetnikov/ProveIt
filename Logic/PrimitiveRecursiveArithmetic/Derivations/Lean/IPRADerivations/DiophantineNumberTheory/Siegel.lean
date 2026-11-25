import IPRADerivations.Core.Powers
import IPRADerivations.Core.CertificateTactics

/-!
# Integral points by squeezing between squares (`siegel_ipra`, `ipra_framework`)

* `siegel_ipra` (`paper/03_runge.tex`): for `m ≥ 1` the integral points of
  `y² = x^{2m} + x + 1` have `x ∈ {0, −1}`. Both signs of `x` are natural-number
  theorems of iPRA, with `m = m' + 1`, `s = t^m` and `m', t, y` variables:
  - `x = t ≥ 0`: `y² = s² + t + 1` forces `t = 0`, since otherwise
    `s² < y² < (s + 1)²`;
  - `x = −t ≤ 0`: `y² + t = s² + 1` forces `t ∈ {0, 1}`, since otherwise
    `(s − 1)² < y² < s²`.
* `ipra_framework` (`paper/sections/07_diophantine.tex`), the integral power gap:
  for natural numbers `a < b` and `m ≥ 1`, `a^m + a^{m−1} ≤ b^m`, so distinct
  `m`-th powers differ by at least `a^{m−1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.Siegel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-! ## The squeeze -/

section Squeeze

/-- Variables: `0 = m'`, `1 = t`, `2 = y`; `s = t^{m'+1}`. -/
abbrev s : PTm 3 := pw (var 1) (succ (var 0))

/-- `y² = s² + t + 1`. -/
abbrev Hpos : Fm PTm 3 := var 2 * var 2 ≐ s * s + var 1 + one

/-- `x = t ≥ 0`: `y² = t^{2m} + t + 1 → t = 0`. -/
abbrev nonnegFormula : Fm PTm 3 := Hpos ⟶ (var 1 ≐ zero)

theorem siegel_nonneg : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 nonnegFormula := by
  refine closeUniv 3 (.impI ?_)
  refine .orE (zero_or_succ (var 1)) Prf.hyp0 ?_
  -- t = S t'; then t ≤ s.
  have ht : ([var 1 ≐ succ (pred (var 1)), Hpos] : List (Fm PTm 3)) ⊢[PRAAx]
      var 1 ≐ succ (pred (var 1)) := Prf.hyp0
  have hts : ([var 1 ≐ succ (pred (var 1)), Hpos] : List (Fm PTm 3)) ⊢[PRAAx] le (var 1) s :=
    le_congr ht.eqSymm (congrAp2 powF (.eqRefl _) ht.eqSymm) (le_self_pw (pred (var 1)) (var 0))
  have w := eq_add_of_le hts
  refine no_square_between (k := s) (y := var 2) _ ?_ ?_
  · refine le_of_eq_add (d := var 1) ?_
    refine withEq Prf.hyp1 fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  · refine le_of_eq_add (d := pred (var 1) + succ (succ zero) * monus s (var 1)) ?_
    refine withEq Prf.hyp1 fun e₁ => withEq ht fun e₂ => withEq w fun e₃ => ?_
    ipra_lc -e₁ + 2 * e₃ + e₂

/-- `y² + t = s² + 1`. -/
abbrev Hneg : Fm PTm 3 := var 2 * var 2 + var 1 ≐ s * s + one

/-- The context of the case `t ≥ 2`. -/
abbrev Θ : List (Fm PTm 3) :=
  [pred (var 1) ≐ succ (pred (pred (var 1))), var 1 ≐ succ (pred (var 1)), Hneg]

/-- `x = −t ≤ 0`: `y² + t = t^{2m} + 1 → t = 0 ∨ t = 1`. -/
abbrev nonposFormula : Fm PTm 3 := Hneg ⟶ ((var 1 ≐ zero) ⋎ (var 1 ≐ one))

theorem siegel_nonpos : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 nonposFormula := by
  refine closeUniv 3 (.impI ?_)
  refine .orE (zero_or_succ (var 1)) (.orI₁ Prf.hyp0) ?_
  refine .orE (zero_or_succ (pred (var 1))) (.orI₂ (Prf.hyp1.eqTrans (congrSucc Prf.hyp0))) ?_
  -- t = S (S t''), so t ≥ 2 and s ≥ t.
  refine .botE _ ?_
  have ht : Θ ⊢[PRAAx] var 1 ≐ succ (succ (pred (pred (var 1)))) :=
    Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
  have hts : Θ ⊢[PRAAx] le (var 1) s :=
    le_congr Prf.hyp1.eqSymm (congrAp2 powF (.eqRefl _) Prf.hyp1.eqSymm) (le_self_pw (pred (var 1)) (var 0))
  have w := eq_add_of_le hts
  -- s = S s' with s' = pred s ≥ 1.
  have hs : Θ ⊢[PRAAx] s ≐ succ (pred s) := by
    refine .orE (zero_or_succ s) ?_ Prf.hyp0
    exact succ_ne_zero' _ (ht.wk.eqSymm.eqTrans (le_antisymm (le_congr (.eqRefl _) Prf.hyp0 hts.wk)
      (zero_le _)))
  refine no_square_between (k := pred s) (y := var 2) _ ?_ ?_
  · refine le_of_eq_add (d := monus s (var 1) + pred s) ?_
    refine withEq hyp2 fun e₁ => withEq ht fun e₂ => withEq w fun e₃ => withEq hs fun e₄ => ?_
    ipra_lc e₁ + e₃ + (Groth.ι (Q.mk Θ s) + Groth.ι (Q.mk Θ (pred s))) * e₄
  · refine le_of_eq_add (d := pred (pred (var 1))) ?_
    refine withEq hyp2 fun e₁ => withEq ht fun e₂ => withEq hs fun e₄ => ?_
    ipra_lc -e₁ + e₂ - (Groth.ι (Q.mk Θ (pred s)) + 1 + Groth.ι (Q.mk Θ s)) * e₄

end Squeeze

/-! ## The power gap -/

section Gap

/-- Variables: `0 = m'` (so `m = m' + 1`), `1 = a`, `2 = b`. -/
abbrev gapFormula : Fm PTm 3 :=
  lt (var 1) (var 2) ⟶ le (pw (var 1) (succ (var 0)) + pw (var 1) (var 0)) (pw (var 2) (succ (var 0)))

theorem power_gap : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 gapFormula := by
  refine closeUniv 3 (ind _ ⟨lt_QF _ _, le_QF _ _⟩ ?_ ?_)
  · pw_subst
    refine .impI (le_congr ?_ (pw_one _).eqSymm Prf.hyp0)
    exact (succ_eq_add_one _).eqTrans (congrAdd (pw_one _).eqSymm (pw_zero _).eqSymm)
  · pw_subst
    refine .impI ?_
    have hab : (lt (var 1) (var 2) :: [gapFormula]) ⊢[PRAAx] lt (var 1) (var 2) := Prf.hyp0
    have ih : (lt (var 1) (var 2) :: [gapFormula]) ⊢[PRAAx]
        le (pw (var 1) (succ (var 0)) + pw (var 1) (var 0)) (pw (var 2) (succ (var 0))) :=
      .impE Prf.hyp1 Prf.hyp0
    -- a^{m+2} + a^{m+1} = (a^{m+1} + a^m) a ≤ b^{m+1} a ≤ b^{m+1} b.
    refine le_congr (a := (pw (var 1) (succ (var 0)) + pw (var 1) (var 0)) * var 1) ?_
      (pw_succ _ _).eqSymm ?_
    · exact (add_mul _ _ _).eqTrans (congrAdd (pw_succ _ _).eqSymm (pw_succ _ _).eqSymm)
    refine le_trans (mul_le_mul_right (var 1) ih) ?_
    exact le_congr (mul_comm _ _) (mul_comm _ _)
      (mul_le_mul_right (pw (var 2) (succ (var 0))) (le_of_lt hab))

end Gap

end LeanProofs.IPRA.DiophantineNumberTheory.Siegel
