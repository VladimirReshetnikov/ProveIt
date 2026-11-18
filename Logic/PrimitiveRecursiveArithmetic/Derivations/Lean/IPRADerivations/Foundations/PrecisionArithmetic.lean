import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Parity
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Foundations.BooleanBits

/-!
# Precision arithmetic for names: tails, inverses, moduli and vanishing errors

Small quantitative lemmas that several packets use to manipulate rational approximations. Rationals are
natural numerators over a common positive denominator supplied by the application, and an absolute value
bound `|a − b| ≤ e` is the pair `a ≤ b + e`, `b ≤ a + e`.

* `tail_replacement` (`foundations/ipra_framework_2026-11-15`, `framework.tex`, Proposition "Finite-tail
  replacement principle"): `|f − F| ≤ e`, `|ℓ − L| ≤ e` and `|f − ℓ| ≤ 2e` give `|F − L| ≤ 4e`
  (with `e = 2^{-(k+2)}`: `|F − L| ≤ 2^{-k}`).
* `apart_lower`, `inverse_error` (the same packet, Lemma "Effective inverse under apartness", `(2)`):
  `|a − x| ≤ ε`, `δ ≤ x` and `2ε ≤ δ` give `δ ≤ 2a`; and then for the difference `d = |x − a| ≤ ε`,
  `d δ² ≤ 2 ε a x`, which is `|1/a − 1/x| ≤ 2ε/δ²` cleared of denominators.
* `cert_compose` (the same packet, Lemma "Finite-certificate composition"): for bits `V₁`, `V₂`, from
  `V₁ = 1 → A = 1` and `V₁ = 1 → V₂ = 1 → B = 1`, the paired verifier `V₁ V₂` satisfies
  `V₁ V₂ = 1 → A = 1 ∧ B = 1`.
* `sum_modulus` (`foundations/ipra_uniformity_framework_2026-11-15`, `thm:mod`, the sum): errors `e` on two
  summands give error `2e` on the sum.
* `lipschitz_modulus` (the same packet, `thm:lipschitz`, "Controlled evaluation"): from
  `|f(x) − f(y)| ≤ L |x − y|`, `L ≤ 2^c` and `|x − y| ≤ 2^{-(k+c)}`, `|f(x) − f(y)| ≤ 2^{-k}`; in numerators,
  `dF ≤ L dx` and `dx 2^{k+c} ≤ den` give `dF 2^k ≤ den`.
* `vanishing_error_at`, `vanishing_error` (`analytic-number-theory/prime_distribution_ipra`,
  `paper/sections/02_foundations.tex`, Lemma "Eliminating a vanishing rational error"): if
  `u ≤ v + c 2^{-s}` for every `s`, then `u ≤ v`. With `u = U/q`, `v = V/q`, `c = C/D`, `D ≥ 1`, the
  hypothesis is `U D 2^s ≤ V D 2^s + C q`, and the precision `s = q C` suffices, since `q C < 2^{q C}`.
  Decidability of the order replaces the case distinction of the paper.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.PrecisionArithmetic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw)
open LeanProofs.IPRA.Foundations.BooleanBits (Bit left_of_band right_of_band)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Tails and sums -/

/-- `|f − F| ≤ e`, `|ℓ − L| ≤ e`, `|f − ℓ| ≤ 2e` give `|F − L| ≤ 4e`. -/
theorem tail_replacement {F L f l e : PTm n} (h₁ : Γ ⊢[PRAAx] le F (f + e)) (h₁' : Γ ⊢[PRAAx] le f (F + e))
    (h₂ : Γ ⊢[PRAAx] le L (l + e)) (h₂' : Γ ⊢[PRAAx] le l (L + e))
    (h₃ : Γ ⊢[PRAAx] le f (l + (e + e))) (h₃' : Γ ⊢[PRAAx] le l (f + (e + e))) :
    Γ ⊢[PRAAx] le F (L + (e + e + e + e)) ⋏ le L (F + (e + e + e + e)) := by
  refine .andI ?_ ?_
  · ipra_le sl h₁ + sl h₃ + sl h₂'
  · ipra_le sl h₂ + sl h₃' + sl h₁'

/-- Errors `e` on two summands give error `2e` on the sum. -/
theorem sum_modulus {q q' r r' e : PTm n} (hq : Γ ⊢[PRAAx] le q (q' + e)) (hr : Γ ⊢[PRAAx] le r (r' + e)) :
    Γ ⊢[PRAAx] le (q + r) (q' + r' + (e + e)) := by
  ipra_le sl hq + sl hr

/-! ## Inversion under apartness -/

/-- `x ≤ a + ε`, `δ ≤ x`, `2ε ≤ δ` give `δ ≤ 2a`. -/
theorem apart_lower {X A E Dl : PTm n} (hXA : Γ ⊢[PRAAx] le X (A + E)) (hD : Γ ⊢[PRAAx] le Dl X)
    (hE : Γ ⊢[PRAAx] le (E + E) Dl) : Γ ⊢[PRAAx] le Dl (A + A) := by
  ipra_le 2 * sl hXA + sl hE + 2 * sl hD

/-- `d ≤ ε`, `δ ≤ 2a`, `δ ≤ x` give `d δ² ≤ 2 ε a x`. -/
theorem inverse_error {X A E Dl d : PTm n} (hd : Γ ⊢[PRAAx] le d E) (hA : Γ ⊢[PRAAx] le Dl (A + A))
    (hD : Γ ⊢[PRAAx] le Dl X) : Γ ⊢[PRAAx] le (d * (Dl * Dl)) ((E + E) * A * X) := by
  ipra_le sl hd * (𝔟 A + 𝔟 A) * 𝔟 X + 𝔟 d * (sl hA * 𝔟 X + 𝔟 Dl * sl hD)

/-! ## Controlled evaluation -/

/-- `dF ≤ L dx`, `L ≤ 2^c` and `dx 2^{k+c} ≤ den` give `dF 2^k ≤ den`. -/
theorem lipschitz_modulus {dF dx L c k den : PTm n} (hL : Γ ⊢[PRAAx] le dF (L * dx))
    (hc : Γ ⊢[PRAAx] le L (pw two c)) (hx : Γ ⊢[PRAAx] le (dx * pw two (k + c)) den) :
    Γ ⊢[PRAAx] le (dF * pw two k) den := by
  have e := natEq (pw_add (Γ := Γ) two k c)
  ipra_le sl hx + 𝔟 (pw two k) * (sl hc * 𝔟 dx + sl hL) using rw [e]; ring

/-! ## Composition of certificates -/

/-- The paired verifier `V₁ V₂` of two bits certifies both conclusions. -/
theorem cert_compose {V₁ V₂ A B : PTm n} (hb₁ : Γ ⊢[PRAAx] Bit V₁) (hb₂ : Γ ⊢[PRAAx] Bit V₂)
    (h₁ : Γ ⊢[PRAAx] (V₁ ≐ one) ⟶ (A ≐ one))
    (h₂ : Γ ⊢[PRAAx] (V₁ ≐ one) ⟶ ((V₂ ≐ one) ⟶ (B ≐ one))) :
    Γ ⊢[PRAAx] (V₁ * V₂ ≐ one) ⟶ ((A ≐ one) ⋏ (B ≐ one)) := by
  refine .impI ?_
  have hv : ((V₁ * V₂ ≐ one) :: Γ) ⊢[PRAAx] V₁ * V₂ ≐ one := Prf.hyp0
  have l := left_of_band hb₁.wk hv
  have r := right_of_band hb₂.wk hv
  exact .andI (Prf.impE h₁.wk l) (Prf.impE (Prf.impE h₂.wk l) r)

/-! ## Eliminating a vanishing rational error -/

/-- If `U D 2^s ≤ V D 2^s + C q` at the precision `s = q C` (with `D = D' + 1`), then `U ≤ V`. -/
theorem vanishing_error_at {U V C D' q : PTm n}
    (h : Γ ⊢[PRAAx] le (U * succ D' * pw two (q * C)) (V * succ D' * pw two (q * C) + C * q)) :
    Γ ⊢[PRAAx] le U V := by
  refine .orE (lt_or_le V U) ?_ Prf.hyp0
  have hV : (lt V U :: Γ) ⊢[PRAAx] le (succ V) U := Prf.hyp0
  have hlt : (lt V U :: Γ) ⊢[PRAAx] le (succ (q * C)) (pw two (q * C)) := lt_pw (le_refl two) (q * C)
  have h' : (lt V U :: Γ) ⊢[PRAAx]
      le (U * succ D' * pw two (q * C)) (V * succ D' * pw two (q * C) + C * q) := h.wk
  have bad : (lt V U :: Γ) ⊢[PRAAx] le (succ (C * q)) (C * q) := by
    ipra_le sl h' + 𝔟 (succ D') * 𝔟 (pw two (q * C)) * sl hV + sl hlt + 𝔟 D' * 𝔟 (pw two (q * C))
  exact lt_irrefl (C * q) _ bad

/-- "Eliminating a vanishing rational error": if `u ≤ v + c 2^{-s}` for every `s`, then `u ≤ v`. -/
theorem vanishing_error {U V C D' q : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (le (Syn.shift U * succ (Syn.shift D') * pw two (var 0))
      (Syn.shift V * succ (Syn.shift D') * pw two (var 0) + Syn.shift C * Syn.shift q))) :
    Γ ⊢[PRAAx] le U V := by
  have a := Prf.allE (q * C) h
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact vanishing_error_at a

end LeanProofs.IPRA.Foundations.PrecisionArithmetic
