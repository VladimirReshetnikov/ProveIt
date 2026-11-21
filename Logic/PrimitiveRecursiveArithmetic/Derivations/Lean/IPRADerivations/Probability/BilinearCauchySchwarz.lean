import IPRADerivations.Probability.Variance
import IPRADerivations.Core.OrderCertificates

/-!
# The bilinear weighted Cauchy–Schwarz inequality on finite tables

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex` (the metrics `d₀, d₁, d₂` on
finite rational tables): "The usual `d₂` inequality follows from finite Cauchy–Schwarz; its square-free kernel
is `(∑ w_i a_i b_i)² ≤ (∑ w_i a_i²)(∑ w_i b_i²)`, proved by expanding the nonnegative sum
`∑_{i,j} w_i w_j (a_i b_j − a_j b_i)²`."

`Probability/FiniteCauchySchwarz` has the case `b_i = 1` over bodies; here the general bilinear form, for an
explicit table of rows `(w_i, a_i, b_i)` of natural terms (weights and absolute values on a common
denominator) of any length, by induction on the table:

* `cross`: `2 (∑ w_i a_i b_i) w a b ≤ (∑ w_i a_i²) w b² + w a² (∑ w_i b_i²)` for one further row
  `(w, a, b)`, the terms `w_i w (a_i b − a b_i)²` of the paper's expansion written with the absolute
  difference `ad`;
* `cauchy_schwarz`: `(∑ w_i a_i b_i)² ≤ (∑ w_i a_i²)(∑ w_i b_i²)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.BilinearCauchySchwarz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `∑ w_i a_i²`. -/
def Saa : List (PTm n × PTm n × PTm n) → PTm n
  | [] => zero
  | p :: ps => p.1 * (p.2.1 * p.2.1) + Saa ps

/-- `∑ w_i b_i²`. -/
def Sbb : List (PTm n × PTm n × PTm n) → PTm n
  | [] => zero
  | p :: ps => p.1 * (p.2.2 * p.2.2) + Sbb ps

/-- `∑ w_i a_i b_i`. -/
def Sab : List (PTm n × PTm n × PTm n) → PTm n
  | [] => zero
  | p :: ps => p.1 * (p.2.1 * p.2.2) + Sab ps

/-- The cross terms against one further row. -/
theorem cross (w a b : PTm n) (L : List (PTm n × PTm n × PTm n)) :
    Γ ⊢[PRAAx] le (num 2 * (Sab L * (w * (a * b)))) (Saa L * (w * (b * b)) + w * (a * a) * Sbb L) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le (num 2 * (zero * (w * (a * b)))) (zero * (w * (b * b)) + w * (a * a) * zero)
    ipra_le 0
  | cons p ps ih =>
    obtain ⟨wi, ai, bi⟩ := p
    show Γ ⊢[PRAAx] le (num 2 * ((wi * (ai * bi) + Sab ps) * (w * (a * b))))
      ((wi * (ai * ai) + Saa ps) * (w * (b * b)) + w * (a * a) * (wi * (bi * bi) + Sbb ps))
    have e := natEq (ad_sq (Γ := Γ) (ai * b) (a * bi))
    ipra_le sl ih + 𝔟 wi * 𝔟 w * 𝔟 (ad (ai * b) (a * bi)) ^ 2 with (𝔟 wi * 𝔟 w) * e

/-- `(∑ w_i a_i b_i)² ≤ (∑ w_i a_i²)(∑ w_i b_i²)`. -/
theorem cauchy_schwarz (L : List (PTm n × PTm n × PTm n)) :
    Γ ⊢[PRAAx] le (Sab L * Sab L) (Saa L * Sbb L) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le (zero * zero) (zero * zero)
    ipra_le 0
  | cons p ps ih =>
    obtain ⟨wi, ai, bi⟩ := p
    show Γ ⊢[PRAAx] le ((wi * (ai * bi) + Sab ps) * (wi * (ai * bi) + Sab ps))
      ((wi * (ai * ai) + Saa ps) * (wi * (bi * bi) + Sbb ps))
    have c := cross (Γ := Γ) wi ai bi ps
    ipra_le sl ih + sl c

end LeanProofs.IPRA.Probability.BilinearCauchySchwarz
