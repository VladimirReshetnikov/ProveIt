import IPRADerivations.Core.OrderCertificates

/-!
# Euclidean norm comparisons, the odd-sphere field and the open-cube chart

Packet: `topology/general_topology_ipra_2026-11-19` (`paper/sections/04_metric.tex`, `07_spheres.tex`). The
dimension `d` is the length of a Lean list of object terms, so each statement is a schema of iPRA derivations,
one for every dimension, with all coordinates arbitrary terms.

* `prop:euclidean-norms`, `‖v‖_∞ ≤ ‖v‖₂ ≤ ‖v‖₁ ≤ d‖v‖_∞`, for the absolute values `v_i` (natural terms),
  squared where a square root occurs: `inf_le_two` (`v_i² ≤ ∑ v_j²`), `two_le_one` (`∑ v_j² ≤ (∑ v_j)²`),
  `one_le_inf` (`∑ v_j ≤ d M` when every `v_j ≤ M`);
* `thm:odd-field` (S07): for `J(x₀, x₁, x₂, x₃, …) = (−x₁, x₀, −x₃, x₂, …)` on integer coordinates,
  `odd_field_tangent` (`x · Jx = 0`) and `odd_field_norm` (`‖Jx‖² = ‖x‖²`);
* `prop:euclidean-open-cube`, the chart `h(t) = t/(1 + |t|)` at `t = a/D`, `h(t) = a/(D + a)`:
  `cube_same_sign` (`a(D + b) − b(D + a) = D(a − b)` for `a = b + c`, and
  `D² c ≤ (D + a)(D + b) c`, i.e. `|h(t) − h(u)| ≤ |t − u|` for `t, u` of the same sign), `cube_opposite`
  (`aD ≤ a(D + a)`, i.e. `|h(t)| ≤ |t|`, which gives the opposite-sign case) and `cube_inverse`
  (`h⁻¹(h(t)) = t`: `a(D + a) = (D + a − a)·a + a·a` cleared, `s/(1 − s) = a/D` for `s = a/(D + a)`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.EuclideanFacts

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `∑ v_j`. -/
def sumL : List (PTm n) → PTm n
  | [] => zero
  | x :: xs => x + sumL xs

/-- `∑ v_j²`. -/
def sqsum : List (PTm n) → PTm n
  | [] => zero
  | x :: xs => x * x + sqsum xs

/-- `‖v‖_∞ ≤ ‖v‖₂`, squared: every `v_i² ≤ ∑ v_j²`. -/
theorem inf_le_two (vs : List (PTm n)) {x : PTm n} (hx : x ∈ vs) :
    Γ ⊢[PRAAx] le (x * x) (sqsum vs) := by
  induction vs with
  | nil => simp at hx
  | cons y ys ih =>
    show Γ ⊢[PRAAx] le (x * x) (y * y + sqsum ys)
    rcases List.mem_cons.mp hx with rfl | hm
    · ipra_le 𝔟 (sqsum ys)
    · have h := ih hm
      ipra_le 𝔟 y * 𝔟 y + sl h

/-- `‖v‖₂ ≤ ‖v‖₁`, squared: `∑ v_j² ≤ (∑ v_j)²`. -/
theorem two_le_one (vs : List (PTm n)) : Γ ⊢[PRAAx] le (sqsum vs) (sumL vs * sumL vs) := by
  induction vs with
  | nil =>
    show Γ ⊢[PRAAx] le zero (zero * zero)
    ipra_le 0
  | cons y ys ih =>
    show Γ ⊢[PRAAx] le (y * y + sqsum ys) ((y + sumL ys) * (y + sumL ys))
    ipra_le 2 * 𝔟 y * 𝔟 (sumL ys) + sl ih

/-- `‖v‖₁ ≤ d‖v‖_∞`: `∑ v_j ≤ d M` when every `v_j ≤ M`. -/
theorem one_le_inf (vs : List (PTm n)) (M : PTm n) (h : ∀ x ∈ vs, Γ ⊢[PRAAx] le x M) :
    Γ ⊢[PRAAx] le (sumL vs) (num vs.length * M) := by
  induction vs with
  | nil =>
    show Γ ⊢[PRAAx] le zero (num 0 * M)
    ipra_le 0
  | cons y ys ih =>
    show Γ ⊢[PRAAx] le (y + sumL ys) (num (ys.length + 1) * M)
    have hy := h y List.mem_cons_self
    have hs := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    ipra_le sl hy + sl hs using
      push_cast; ring

/-- `x · Jx` for coordinate pairs `(x_{2i}, x_{2i+1})`. -/
def jdot : List (ZT n × ZT n) → ZT n
  | [] => ZT.natLit 0
  | p :: ps => p.1 * -p.2 + p.2 * p.1 + jdot ps

/-- `‖Jx‖²`. -/
def jnorm : List (ZT n × ZT n) → ZT n
  | [] => ZT.natLit 0
  | p :: ps => -p.2 * -p.2 + p.1 * p.1 + jnorm ps

/-- `‖x‖²`. -/
def xnorm : List (ZT n × ZT n) → ZT n
  | [] => ZT.natLit 0
  | p :: ps => p.1 * p.1 + p.2 * p.2 + xnorm ps

private theorem jdot_toZ (ps : List (ZT n × ZT n)) : ZT.toZ Γ (jdot ps) = 0 := by
  induction ps with
  | nil => simp [jdot]
  | cons p ps ih => simp only [jdot, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ih]; ring

private theorem jnorm_toZ (ps : List (ZT n × ZT n)) : ZT.toZ Γ (jnorm ps) = ZT.toZ Γ (xnorm ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [jnorm, xnorm, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ih]; ring

/-- S07: `Jx` is tangent, `x · Jx = 0`. -/
theorem odd_field_tangent (ps : List (ZT n × ZT n)) : Γ ⊢[PRAAx] ZT.eq (jdot ps) (ZT.natLit 0) := by
  apply ZT.derive
  rw [jdot_toZ]; simp

/-- S07: `‖Jx‖² = ‖x‖²`, so `J` does not vanish on the sphere. -/
theorem odd_field_norm (ps : List (ZT n × ZT n)) : Γ ⊢[PRAAx] ZT.eq (jnorm ps) (xnorm ps) :=
  ZT.derive (jnorm_toZ ps)

/-- The open-cube chart on one sign: `a(D + b) = b(D + a) + Dc` and `D²c ≤ (D + a)(D + b)c` for `a = b + c`. -/
theorem cube_same_sign (D b c : PTm n) :
    (Γ ⊢[PRAAx] (b + c) * (D + b) ≐ b * (D + (b + c)) + D * c) ∧
    (Γ ⊢[PRAAx] le (D * D * c) ((D + (b + c)) * (D + b) * c)) := by
  refine ⟨?_, ?_⟩
  · ipra_ring
  · ipra_le (𝔟 D * (2 * 𝔟 b + 𝔟 c) + (𝔟 b + 𝔟 c) * 𝔟 b) * 𝔟 c

/-- `|h(t)| ≤ |t|`: `aD ≤ a(D + a)`. -/
theorem cube_opposite (D a : PTm n) : Γ ⊢[PRAAx] le (a * D) (a * (D + a)) := by
  ipra_le 𝔟 a * 𝔟 a

/-- `h⁻¹(h(t)) = t`, cleared: for `s = a/(D + a)`, `s · D = (1 − s) · a` reads `a · D = D · a` over `D + a`. -/
theorem cube_inverse (D a : PTm n) : Γ ⊢[PRAAx] a * (monus (D + a) a) ≐ D * a := by
  apply deriveNat; ipra_simps
  rw [natEq (add_monus (Γ := Γ) D a)]; ring

end LeanProofs.IPRA.Topology.EuclideanFacts
