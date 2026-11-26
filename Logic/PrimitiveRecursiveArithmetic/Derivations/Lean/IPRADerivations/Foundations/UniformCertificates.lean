import IPRADerivations.Core.Division
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Arithmetic of uniform certificates: grid indices, error transport, implicit roots

Packet: `foundations/ipra_uniform_certificates`, `framework.tex`. Rationals are natural numerators over a
common positive denominator and `|a − b| ≤ e` is the pair `a ≤ b + e`, `b ≤ a + e`.

`thm:net` ("Uniform finite-net lifting"), for a rational input `x = p/q ∈ [0, 1]` and a mesh `M`:

* `grid_lower`, `grid_upper`: the nearest-left grid index `j = ⌊M p / q⌋` satisfies `j q ≤ M p ≤ j q + q`,
  i.e. `0 ≤ x − j/M ≤ 1/M` (the Euclidean division invariant of the proof);
* `grid_clip`: for `p ≤ q` the index is already clipped, `j ≤ M`;
* `net_error`: the modulus error `|F(x) − F(j/M)| ≤ e₁` and the sample error `|q_j − F(j/M)| ≤ e₂` add up,
  `F(x) ≤ q_j + (e₂ + e₁)` (and symmetrically, by the same rule).

The error transport rule of the section "Compositional precision calculus":

* `error_transport`: `|f(u) − f(u′)| ≤ K ε` and a stage error `|f̃(u′) − f(u′)| ≤ η` give
  `|f̃(u′) − f(u)| ≤ K ε + η` (one direction; the other is the same rule with the roles exchanged).

`thm:implicit` ("Certified uniform implicit root"), the two consequences of the separation certificate
`c (y − z)² ≤ (y − z)(P(x, y) − P(x, z))`, with `d = |y − z|` and `g = |P(x, y) − P(x, z)|`:

* `root_lipschitz`: with `g ≤ L |x − x′|` (roots at `x` and `x′`), `c d ≤ L |x − x′|`. The cancellation
  of `d` is by the decidable case `d = 0 ∨ d > 0`, not by a decision on represented reals;
* `root_unique`: with `g = 0` and `c ≥ 1`, `d = 0`.

The bisection name itself (`lem:bisect`), the represented-input adapter and the cover selection are not
derived here; for the cubic chart of the corollary see `Foundations/StableCubicRoot`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.UniformCertificates

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The nearest-left grid index -/

/-- `j q ≤ M p` for `j = ⌊M p / q⌋`, `q = q′ + 1`. -/
theorem grid_lower (M p q' : PTm n) :
    Γ ⊢[PRAAx] le (quo (M * p) (succ q') * succ q') (M * p) := by
  have dm := div_mod (Γ := Γ) (M * p) q'
  have e := natEq (Prf.andE₁ dm)
  ipra_le 𝔟 (rem (M * p) (succ q')) using linear_combination e

/-- `M p ≤ j q + q` for `j = ⌊M p / q⌋`. -/
theorem grid_upper (M p q' : PTm n) :
    Γ ⊢[PRAAx] le (M * p) (quo (M * p) (succ q') * succ q' + succ q') := by
  have dm := div_mod (Γ := Γ) (M * p) q'
  have e := natEq (Prf.andE₁ dm)
  have hr : Γ ⊢[PRAAx] le (succ (rem (M * p) (succ q'))) (succ q') := Prf.andE₂ dm
  ipra_le sl hr + 1 using linear_combination -e

/-- For `p ≤ q` the grid index is at most the mesh: `j ≤ M`. -/
theorem grid_clip {M p q' : PTm n} (hp : Γ ⊢[PRAAx] le p (succ q')) :
    Γ ⊢[PRAAx] le (quo (M * p) (succ q')) M := by
  have dm := div_mod (Γ := Γ) (M * p) q'
  have e := natEq (Prf.andE₁ dm)
  have h : Γ ⊢[PRAAx] le (succ q' * quo (M * p) (succ q')) (succ q' * M) := by
    ipra_le 𝔟 M * sl hp + 𝔟 (rem (M * p) (succ q')) using linear_combination e
  exact mul_le_cancel h

/-! ## Adding errors -/

/-- The triangle rule for one-sided bounds: `a ≤ b + e₁` and `b ≤ c + e₂` give `a ≤ c + (e₂ + e₁)`. -/
theorem triangle {a b c e₁ e₂ : PTm n} (h₁ : Γ ⊢[PRAAx] le a (b + e₁)) (h₂ : Γ ⊢[PRAAx] le b (c + e₂)) :
    Γ ⊢[PRAAx] le a (c + (e₂ + e₁)) := by
  ipra_le sl h₁ + sl h₂

/-- `thm:net`: the modulus error and the sample error add up. -/
theorem net_error {Fx Fg qv e₁ e₂ : PTm n} (hmod : Γ ⊢[PRAAx] le Fx (Fg + e₁))
    (hsample : Γ ⊢[PRAAx] le Fg (qv + e₂)) : Γ ⊢[PRAAx] le Fx (qv + (e₂ + e₁)) :=
  triangle hmod hsample

/-- The error transport rule: a stage error `η` after a `K`-Lipschitz transport of an input error `ε`. -/
theorem error_transport {A B C K ε η : PTm n} (hstage : Γ ⊢[PRAAx] le A (B + η))
    (hlip : Γ ⊢[PRAAx] le B (C + K * ε)) : Γ ⊢[PRAAx] le A (C + (K * ε + η)) :=
  triangle hstage hlip

/-! ## Implicit roots from a separation certificate -/

/-- `thm:implicit`, the Lipschitz bound: `c d² ≤ d g` and `g ≤ L e` give `c d ≤ L e`. -/
theorem root_lipschitz {c d g L e : PTm n} (hsep : Γ ⊢[PRAAx] le (c * (d * d)) (d * g))
    (hlip : Γ ⊢[PRAAx] le g (L * e)) : Γ ⊢[PRAAx] le (c * d) (L * e) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have k := natEq (Prf.hyp0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero)
    ipra_le 𝔟 L * 𝔟 e using rw [k]; ring
  · have k := natEq (Prf.hyp0 : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d))
    have hsep' := hsep.wk (ψ := d ≐ succ (pred d))
    have h' : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] le (succ (pred d) * (c * d)) (succ (pred d) * g) := by
      ipra_le sl hsep' using linear_combination (-(𝔟 g - 𝔟 c * 𝔟 d)) * k
    exact le_trans (mul_le_cancel h') hlip.wk

/-- `thm:implicit`, uniqueness: `c d² ≤ d g` with `c ≥ 1` and `g = 0` gives `d = 0`. -/
theorem root_unique {c' d g : PTm n} (hsep : Γ ⊢[PRAAx] le (succ c' * (d * d)) (d * g))
    (hg : Γ ⊢[PRAAx] g ≐ zero) : Γ ⊢[PRAAx] d ≐ zero := by
  have k₀ := natEq hg
  have hz : Γ ⊢[PRAAx] le g (zero * zero) := by ipra_le 0 using linear_combination -k₀
  have h := root_lipschitz hsep hz
  refine .orE (zero_or_succ d) Prf.hyp0 ?_
  have k := natEq (Prf.hyp0 : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d))
  have h' := h.wk (ψ := d ≐ succ (pred d))
  refine not_succ_le_self zero _ ?_
  ipra_le sl h' + 𝔟 c' * 𝔟 d + 𝔟 (pred d) using linear_combination k

end LeanProofs.IPRA.Foundations.UniformCertificates
