import IPRADerivations.Core.Powers
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Parity
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# The natural-number height contraction of a descent step

Packet: `diophantine-number-theory/mordell_weil_ipra`, `paper/03_elliptic.tex`, Lemma `lem:bitcontract`
("A natural-number contraction"): "Whenever `P = 2Q + R_i`, one has `H(Q)⁴ ≤ D H(P)²`,
`2h(Q) ≤ h(P) + C`", the second from the first: "if `h(Q) = 0` there is nothing to prove. Otherwise the
definition of `h` gives `2^{h(Q)−1} < H(Q)`, while `D ≤ 2^d` and `H(P) ≤ 2^{h(P)}`. Comparing powers of
two yields `4(h(Q) − 1) < d + 2h(P)`."

* `pw_exp_mono`: `e ≤ f` gives `2^e ≤ 2^f`;
* `exponent_compare`: from `H(Q)⁴ ≤ D H(P)²`, `2^{h′} < H(Q)`, `D ≤ 2^d` and `H(P) ≤ 2^{h(P)}`:
  `4h′ < d + 2h(P)` (here `h(Q) = h′ + 1`);
* `height_contraction`: with any `C` such that `d + 3 ≤ 2C`, `2h(Q) ≤ h(P) + C`.

The multiplicative estimate `H(Q)⁴ ≤ D H(P)²` (from the duplication and translation bounds) and the
definition of the logarithmic height `h` by binary length are inputs; the case `h(Q) = 0` is trivial.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.HeightContraction

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `e ≤ f` gives `2^e ≤ 2^f`. -/
theorem pw_exp_mono {e f : PTm n} (h : Γ ⊢[PRAAx] le e f) : Γ ⊢[PRAAx] le (pw two e) (pw two f) := by
  have eA := natEq ((congrAp2 powF (eq_add_of_le h) (.eqRefl (two : PTm n))).eqTrans
    (pw_add (Γ := Γ) two e (monus f e)))
  have eB := natEq (pw_pos (Γ := Γ) one (monus f e))
  ipra_le 𝔟(pw two e) * 𝔟(pred (pw (succ one) (monus f e))) using
    linear_combination eA + 𝔟(pw two e) * eB

/-- `lem:bitcontract`: comparing powers of two, `4h′ < d + 2h(P)`. -/
theorem exponent_compare {HQ HP D hQ' hP d : PTm n}
    (h₁ : Γ ⊢[PRAAx] le (HQ * HQ * (HQ * HQ)) (D * (HP * HP)))
    (h₂ : Γ ⊢[PRAAx] lt (pw two hQ') HQ)
    (h₃ : Γ ⊢[PRAAx] le D (pw two d))
    (h₄ : Γ ⊢[PRAAx] le HP (pw two hP)) :
    Γ ⊢[PRAAx] lt (hQ' + hQ' + (hQ' + hQ')) (d + (hP + hP)) := by
  have h₂' : Γ ⊢[PRAAx] le (succ (pw two hQ')) HQ := h₂
  have hA := sq_le_sq (sq_le_sq h₂')
  have hC := le_mul_mono h₃ (le_mul_mono h₄ h₄)
  have chain : Γ ⊢[PRAAx] le (succ (pw two hQ') * succ (pw two hQ') *
      (succ (pw two hQ') * succ (pw two hQ'))) (pw two d * (pw two hP * pw two hP)) :=
    le_trans hA (le_trans h₁ hC)
  have e₁ : Γ ⊢[PRAAx] pw two (d + (hP + hP)) ≐ pw two d * (pw two hP * pw two hP) :=
    (pw_add two d (hP + hP)).eqTrans (congrMul (.eqRefl _) (pw_add two hP hP))
  have e₂ : Γ ⊢[PRAAx] pw two (hQ' + hQ' + (hQ' + hQ')) ≐
      pw two hQ' * pw two hQ' * (pw two hQ' * pw two hQ') :=
    (pw_add two (hQ' + hQ') (hQ' + hQ')).eqTrans (congrMul (pw_add two hQ' hQ') (pw_add two hQ' hQ'))
  refine .orE (lt_or_le (hQ' + hQ' + (hQ' + hQ')) (d + (hP + hP))) Prf.hyp0 ?_
  have pm := le_congr e₁.wk e₂.wk (pw_exp_mono (Prf.hyp0 :
    (le (d + (hP + hP)) (hQ' + hQ' + (hQ' + hQ')) :: Γ) ⊢[PRAAx] _))
  have fin := le_trans chain.wk pm
  have abs : (le (d + (hP + hP)) (hQ' + hQ' + (hQ' + hQ')) :: Γ) ⊢[PRAAx]
      le (succ (pw two hQ' * pw two hQ' * (pw two hQ' * pw two hQ')))
        (pw two hQ' * pw two hQ' * (pw two hQ' * pw two hQ')) := by
    ipra_le sl fin + 4 * 𝔟(pw two hQ') * 𝔟(pw two hQ') * 𝔟(pw two hQ') +
      6 * 𝔟(pw two hQ') * 𝔟(pw two hQ') + 4 * 𝔟(pw two hQ')
  exact not_succ_le_self _ _ abs

/-- `lem:bitcontract`: `2h(Q) ≤ h(P) + C` for `h(Q) = h′ + 1` and any `C` with `d + 3 ≤ 2C`. -/
theorem height_contraction {HQ HP D hQ' hP d C : PTm n}
    (h₁ : Γ ⊢[PRAAx] le (HQ * HQ * (HQ * HQ)) (D * (HP * HP)))
    (h₂ : Γ ⊢[PRAAx] lt (pw two hQ') HQ)
    (h₃ : Γ ⊢[PRAAx] le D (pw two d))
    (h₄ : Γ ⊢[PRAAx] le HP (pw two hP))
    (hC : Γ ⊢[PRAAx] le (d + num 3) (two * C)) :
    Γ ⊢[PRAAx] le (two * succ hQ') (hP + C) := by
  have cl := exponent_compare h₁ h₂ h₃ h₄
  have cl' : Γ ⊢[PRAAx] le (succ (hQ' + hQ' + (hQ' + hQ'))) (d + (hP + hP)) := cl
  have key : Γ ⊢[PRAAx] le (succ one * (two * succ hQ')) (succ one * (hP + C)) := by
    ipra_le sl cl' + sl hC
  exact mul_le_cancel key

end LeanProofs.IPRA.DiophantineNumberTheory.HeightContraction
