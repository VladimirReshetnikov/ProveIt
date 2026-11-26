import IPRADerivations.Core.OrderCertificates

/-!
# Gauss–Bonnet: the incidence polynomial and the residual bounds

Packet: `geometry/gauss_bonnet_ipra`, `paper/sections/05_global.tex`, `06_arithmetic.tex` and `lean/IPRABridge.lean`
(the packet's object-level candidate, adapted here and compiled against this workspace).

* `incidence_polynomial`: from `3F = 2E_i + E_b` and `E_b = V_b`,
  `p (2V_i + V_b + 2(E_i + E_b)) = p (2(V_i + V_b + F) + F)`, the sign-free form of the Euler coefficient identity
  `2χ = 2V_i + V_b − F` multiplied by a natural numerator `p`;
* `residual_upper`, `residual_lower`: the two sides of `|R − I + S| ≤ b_F + b_E + b_V` from the three bounds on the
  face, edge and vertex residuals, with signed quantities as positive and negative parts.

These are the finite arithmetic steps of the global assembly only. The presentation hypotheses, the discrete Green
identity, the triangle turning and the quantitative Gauss–Bonnet theorem of the packet are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.GaussBonnetBridge
open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (Q.mk Γ t)

/-- Sign-free form of the Euler coefficient identity, multiplied by an
    arbitrary natural numerator p. Signed rationals are encoded by pairs,
    and denominators are cleared before invoking this lemma. -/
theorem incidence_polynomial
    (p vi vb ei eb f : PTm n)
    (hf : Γ ⊢[PRAAx] num 3 * f ≐ num 2 * ei + eb)
    (hb : Γ ⊢[PRAAx] eb ≐ vb) :
    Γ ⊢[PRAAx]
      p * (num 2 * vi + vb + num 2 * (ei + eb)) ≐
        p * (num 2 * (vi + vb + f) + f) := by
  ipra_lc -(𝔟 p) * natEq hf + (𝔟 p) * natEq hb

/-- If R <= bf, -I <= be, and S <= bv, then R-I+S <= bf+be+bv.
    Positive/negative parts avoid integer subtraction in the object language. -/
theorem residual_upper
    (rp rm ip im sp sm bf be bv : PTm n)
    (hF : Γ ⊢[PRAAx] le rp (rm + bf))
    (hE : Γ ⊢[PRAAx] le im (ip + be))
    (hV : Γ ⊢[PRAAx] le sp (sm + bv)) :
    Γ ⊢[PRAAx] le (rp + im + sp) (rm + ip + sm + (bf + be + bv)) := by
  ipra_le sl hF + sl hE + sl hV

/-- The other side of the absolute-value estimate. -/
theorem residual_lower
    (rp rm ip im sp sm bf be bv : PTm n)
    (hF : Γ ⊢[PRAAx] le rm (rp + bf))
    (hE : Γ ⊢[PRAAx] le ip (im + be))
    (hV : Γ ⊢[PRAAx] le sm (sp + bv)) :
    Γ ⊢[PRAAx] le (rm + ip + sm) (rp + im + sp + (bf + be + bv)) := by
  ipra_le sl hF + sl hE + sl hV

end LeanProofs.IPRA.Geometry.GaussBonnetBridge
