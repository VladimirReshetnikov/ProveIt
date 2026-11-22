import IPRADerivations.Core.OrderCertificates

/-!
# The finite polynomial and inequality steps as deep iPRA judgments

Status: source candidate, NOT compiler-checked in the authoring environment.
Intended import environment: VladimirReshetnikov/ProveIt, commit
d36b35eed5bd01af4ade66bf539622495813ccc8,
Logic/PrimitiveRecursiveArithmetic/Derivations/Lean.

Unlike Assembly.lean, these conclusions are `Prf PRAAx` judgments. They do not
formalize the geometric hypotheses, the finite grid construction, or the full
smooth theorem. No `sorry` declarations or new axioms are used.
-/

namespace LeanProofs.IPRA.Geometry.GaussBonnet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

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
  have ef := natEq hf
  have ebv := natEq hb
  apply deriveNat
  ipra_simps
  linear_combination -(𝔟 p) * ef + (𝔟 p) * ebv

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

end LeanProofs.IPRA.Geometry.GaussBonnet
