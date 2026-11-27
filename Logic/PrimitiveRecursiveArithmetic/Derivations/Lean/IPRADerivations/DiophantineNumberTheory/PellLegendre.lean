import IPRADerivations.DiophantineNumberTheory.RungeProduct
import IPRADerivations.Core.OrderCertificates

/-!
# Legendre's theorem in finite form

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:legendre` ("Legendre, in finite
form"): "If `p ∈ ℤ`, `q ≥ 1`, and `|s − p/q| < 1/(2q²)`, then `p/q = p_n/q_n` … If the two rational
numbers differed, their nonzero integer determinant would satisfy
`1 ≤ |p q_n − q p_n| ≤ q_n |p − q s| + q |q_n s − p_n| ≤ (q_n + q) E ≤ 2qE < 1`, which is impossible."

For a rational `s = σ/τ` (all quantities signed integer terms, `Core/Integers`) and the integer absolute
value `za` of `DiophantineNumberTheory/RungeProduct`, with `e = τp − qσ` (`τ` times the error of `p/q`)
and `e′ = τp_n − q_nσ`:

* `det_identity`: `τ (p q_n − q p_n) = q_n e − q e′`;
* `det_bound`: `|τ| |p q_n − q p_n| ≤ 2 |q| |e|`, using `|q_n| ≤ |q|` and `|e′| ≤ |e|` (the best
  approximation of the second kind, `lem:bestsecond`, for the convergent `p_n/q_n` with `q_n ≤ q`);
* `legendre_finite`: if moreover `2 |q| |e| < |τ|` (the hypothesis `|s − p/q| < 1/(2q²)`, cleared), then
  `|p q_n − q p_n| = 0`, i.e. `p/q = p_n/q_n`.

The convergents, the choice of `n` and the best-approximation lemma itself are inputs.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellLegendre

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.RungeProduct (za D_congr D_neg D_add_le D_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `τ (p q_n − q p_n) = q_n (τp − qσ) − q (τp_n − q_nσ)`. -/
theorem det_identity (τ σ p q pn qn : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (τ * (p * qn + -(q * pn)))
      (qn * (τ * p + -(q * σ)) + -(q * (τ * pn + -(qn * σ)))) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg]
    ring)

/-- `|τ| |p q_n − q p_n| ≤ 2 |q| |e|` from `|q_n| ≤ |q|` and `|e′| ≤ |e|`. -/
theorem det_bound {τ σ p q pn qn : ZT n}
    (h₁ : Γ ⊢[PRAAx] le (za qn) (za q))
    (h₂ : Γ ⊢[PRAAx] le (za (τ * pn + -(qn * σ))) (za (τ * p + -(q * σ)))) :
    Γ ⊢[PRAAx] le (za τ * za (p * qn + -(q * pn))) (two * (za q * za (τ * p + -(q * σ)))) := by
  have t := D_add_le (Γ := Γ) (qn * (τ * p + -(q * σ))) (-(q * (τ * pn + -(qn * σ))))
  have hB := le_congr (D_congr (det_identity τ σ p q pn qn)).eqSymm
    (congrAdd (D_mul qn _) ((D_neg _).eqTrans (D_mul q _))) t
  have hB' := le_congr (D_mul τ _) (.eqRefl _) hB
  ipra_le sl hB' + (𝔟(monus (τ * p + -(q * σ)).pos (τ * p + -(q * σ)).neg) +
      𝔟(monus (τ * p + -(q * σ)).neg (τ * p + -(q * σ)).pos)) * sl h₁ +
    (𝔟(monus q.pos q.neg) + 𝔟(monus q.neg q.pos)) * sl h₂

/-- `thm:legendre`, finite form: the determinant `p q_n − q p_n` vanishes. -/
theorem legendre_finite {τ σ p q pn qn : ZT n}
    (h₁ : Γ ⊢[PRAAx] le (za qn) (za q))
    (h₂ : Γ ⊢[PRAAx] le (za (τ * pn + -(qn * σ))) (za (τ * p + -(q * σ))))
    (h₃ : Γ ⊢[PRAAx] lt (two * (za q * za (τ * p + -(q * σ)))) (za τ)) :
    Γ ⊢[PRAAx] za (p * qn + -(q * pn)) ≐ zero := by
  have b := det_bound h₁ h₂
  refine .orE (zero_or_succ (za (p * qn + -(q * pn)))) Prf.hyp0 ?_
  have pos := natEq (Prf.hyp0 : ((za (p * qn + -(q * pn)) ≐ succ (pred (za (p * qn + -(q * pn))))) :: Γ)
    ⊢[PRAAx] _)
  have b' := b.wk (ψ := za (p * qn + -(q * pn)) ≐ succ (pred (za (p * qn + -(q * pn)))))
  have h₃' : ((za (p * qn + -(q * pn)) ≐ succ (pred (za (p * qn + -(q * pn))))) :: Γ) ⊢[PRAAx]
      le (succ (two * (za q * za (τ * p + -(q * σ))))) (za τ) := h₃.wk
  have abs : ((za (p * qn + -(q * pn)) ≐ succ (pred (za (p * qn + -(q * pn))))) :: Γ) ⊢[PRAAx]
      le (succ (two * (za q * za (τ * p + -(q * σ))))) (two * (za q * za (τ * p + -(q * σ)))) := by
    ipra_le sl h₃' + sl b' +
      (𝔟(monus τ.pos τ.neg) + 𝔟(monus τ.neg τ.pos)) * 𝔟(pred (za (p * qn + -(q * pn)))) using
      linear_combination (𝔟(monus τ.pos τ.neg) + 𝔟(monus τ.neg τ.pos)) * pos
  exact not_succ_le_self _ _ abs

end LeanProofs.IPRA.DiophantineNumberTheory.PellLegendre
