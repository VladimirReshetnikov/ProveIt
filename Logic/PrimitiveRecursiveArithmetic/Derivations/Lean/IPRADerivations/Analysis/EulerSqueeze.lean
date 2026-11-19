import IPRADerivations.Analysis.EulerBrackets

/-!
# The squeeze lemmas and the bracket width of the Bohr–Mollerup argument

Packet: `analysis/bohr_mollerup_ipra_2026-11-15`, `paper/bohr_mollerup_ipra.tex`.

For a rational `q = a/b`, `b = a + c`, the paper compares a function `F` satisfying the Bohr–Mollerup
conditions with the Euler brackets `A_n(q) ≤ B_n(q)` after raising to the `b`-th power. The values of `F`
and the rational factors enter only through finitely many numbers, which are parameters here (numerators
over a common denominator); the instance of rational multiplicative convexity is a hypothesis.

* `upper_squeeze` (`eq:upper-squeeze`): from `F(n + q) = P_n(q) F(q)` (as `w X = P Y`),
  `F(n + 1) = n F(n)` (as `H = N G`) and the convexity instance `F(n + q)^b ≤ F(n)^{b−a} F(n + 1)^a`
  (as `X^{a+c} ≤ G^c H^a`): `P^b Y^b ≤ w^b G^b N^a`, i.e. `F(q)^b ≤ ((n−1)!)^b n^a / P_n(q)^b = B_n(q)^b`.
* `lower_squeeze` (`eq:lower-squeeze`): from `w X = P Y`, `F(n + q + 1) = (n + q) F(n + q)` (as
  `v Z = m X`) and the convexity instance `F(n + 1)^b ≤ F(n + q)^a F(n + q + 1)^{b−a}` (as
  `H^{a+c} ≤ X^a Z^c`): `v^c w^b H^b ≤ m^c P^b Y^b`, i.e.
  `F(q)^b ≥ (n!)^b / (P_n(q)^b (n + q)^{b−a}) = A_n(q)^b`.
* `bracket_order`, `bracket_width` (`eq:BoverA`, `eq:width`): from `n b B = (n b + a) A`, `A ≤ B`, and
  with `A ≤ 1/q` on the scale `S` (as `a A ≤ b S`), `n (B − A) ≤ S` (cleared by `b`).
* `raw_width` (`eq:raw-width`): for root bounds `ρ⁻ ≤ r ≤ ρ⁺` of width at most `δ` and the endpoints
  `ℓ = c_A ρ⁻`, `u = c_B ρ⁺`: `u − ℓ ≤ (c_B r − c_A r) + (c_A + c_B) δ`.

The iterated recurrence `eq:recurrence-iterated`, the reading of the algebraic endpoint `n^q` through its
bisection name, convergence and the Bohr–Mollerup theorem itself are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EulerSqueeze

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `eq:upper-squeeze`: `P^b Y^b ≤ w^b G^b N^a` for `b = a + c`. -/
theorem upper_squeeze {a c w X P Y G H N : PTm n}
    (hX : Γ ⊢[PRAAx] w * X ≐ P * Y) (hH : Γ ⊢[PRAAx] H ≐ N * G)
    (hc : Γ ⊢[PRAAx] le (pw X (a + c)) (pw G c * pw H a)) :
    Γ ⊢[PRAAx] le (pw P (a + c) * pw Y (a + c)) (pw w (a + c) * (pw G (a + c) * pw N a)) := by
  have e₁ := natEq (pw_mul_base (Γ := Γ) w X (a + c))
  have e₂ := natEq (pw_mul_base (Γ := Γ) P Y (a + c))
  have e₃ := natEq (congrAp2 powF (Prf.eqRefl (a + c)) hX)
  have E₂ := e₁.symm.trans (e₃.trans e₂)
  have eH := (natEq (congrAp2 powF (Prf.eqRefl a) hH)).trans (natEq (pw_mul_base (Γ := Γ) N G a))
  have eG := natEq (pw_add (Γ := Γ) G a c)
  ipra_le 𝔟 (pw w (a + c)) * sl hc using
    linear_combination E₂ + 𝔟 (pw w (a + c)) * 𝔟 (pw N a) * eG - 𝔟 (pw w (a + c)) * 𝔟 (pw G c) * eH

/-- `eq:lower-squeeze`: `v^c w^b H^b ≤ m^c P^b Y^b` for `b = a + c`. -/
theorem lower_squeeze {a c w v m X Z P Y H : PTm n}
    (hX : Γ ⊢[PRAAx] w * X ≐ P * Y) (hZ : Γ ⊢[PRAAx] v * Z ≐ m * X)
    (hc : Γ ⊢[PRAAx] le (pw H (a + c)) (pw X a * pw Z c)) :
    Γ ⊢[PRAAx] le (pw v c * pw w (a + c) * pw H (a + c)) (pw m c * (pw P (a + c) * pw Y (a + c))) := by
  have e₁ := natEq (pw_mul_base (Γ := Γ) w X (a + c))
  have e₂ := natEq (pw_mul_base (Γ := Γ) P Y (a + c))
  have e₃ := natEq (congrAp2 powF (Prf.eqRefl (a + c)) hX)
  have E₂ := e₁.symm.trans (e₃.trans e₂)
  have f₁ := natEq (pw_mul_base (Γ := Γ) v Z c)
  have f₂ := natEq (pw_mul_base (Γ := Γ) m X c)
  have f₃ := natEq (congrAp2 powF (Prf.eqRefl c) hZ)
  have E₁ := f₁.symm.trans (f₃.trans f₂)
  have eX := natEq (pw_add (Γ := Γ) X a c)
  ipra_le 𝔟 (pw v c) * 𝔟 (pw w (a + c)) * sl hc using
    linear_combination (-𝔟 (pw m c)) * E₂ + 𝔟 (pw m c) * 𝔟 (pw w (a + c)) * eX
      - 𝔟 (pw w (a + c)) * 𝔟 (pw X a) * E₁

/-- `eq:BoverA` gives `A_n ≤ B_n`. -/
theorem bracket_order {N b a Av Bv : PTm n} (hBA : Γ ⊢[PRAAx] N * b * Bv ≐ (N * b + a) * Av) :
    Γ ⊢[PRAAx] le (N * b * Av) (N * b * Bv) := by
  have e := natEq hBA
  ipra_le 𝔟 a * 𝔟 Av using linear_combination e

/-- `eq:width`: `n (B_n − A_n) ≤ S` when `A_n ≤ 1/q` on the scale `S`; cleared by `b`. -/
theorem bracket_width {N b a Av Bv S : PTm n} (hBA : Γ ⊢[PRAAx] N * b * Bv ≐ (N * b + a) * Av)
    (hA : Γ ⊢[PRAAx] le (a * Av) (b * S)) :
    Γ ⊢[PRAAx] le (b * (N * Bv)) (b * (N * Av + S)) := by
  have e := natEq hBA
  ipra_le sl hA using linear_combination -e

/-- `eq:raw-width`: `c_B ρ⁺ − c_A ρ⁻ ≤ (c_B r − c_A r) + (c_A + c_B) δ` for `ρ⁻ ≤ r ≤ ρ⁺ ≤ ρ⁻ + δ`. -/
theorem raw_width {cA cB r lo hi δ : PTm n} (hlo : Γ ⊢[PRAAx] le lo r) (hhi : Γ ⊢[PRAAx] le r hi)
    (hδ : Γ ⊢[PRAAx] le hi (lo + δ)) :
    Γ ⊢[PRAAx] le (cB * hi + cA * r) (cA * lo + cB * r + (cA + cB) * δ) := by
  ipra_le 𝔟 cB * (sl hδ + sl hlo) + 𝔟 cA * (sl hδ + sl hhi)

end LeanProofs.IPRA.Analysis.EulerSqueeze
