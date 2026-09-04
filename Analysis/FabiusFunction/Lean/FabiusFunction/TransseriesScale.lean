import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotic scales and Poincaré expansions

The transseries volume's `q0:def:scale`, `q0:def:poincare` and
`q0:prop:uniqueness`, the vocabulary the rest of that volume is written in.

An *asymptotic scale* along a filter is a sequence of eventually nonvanishing
functions with `φ (n+1) = o(φ n)`.  A *Poincaré expansion* of `f` on that scale
is a coefficient sequence `a` with

`f - ∑_{n < N} aₙ φₙ = O(φ_N)` for every fixed `N`,

the number of retained terms being fixed before the limit is taken; no
convergence is claimed, and in the cases the volume cares about there is none.

The substantive result is that the coefficients are determined by `f` and the
scale, through the explicit limit

`a_N = lim (f - ∑_{n < N} aₙ φₙ) / φ_N`,

so two different coefficient sequences cannot represent the same `f` on the
same scale.  The proof is the one-line observation that the `N+1`-st condition
turns the `N`-th remainder into `a_N φ_N + o(φ_N)`.

Nothing here is specific to the polynomial–logarithmic scale: `𝕜` is any normed
field and `l` any filter, so the special-function parts of the volume can build
their own models on this.
-/

set_option autoImplicit false

open Filter Asymptotics Finset
open scoped Topology

namespace Fabius

variable {α 𝕜 E : Type*} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {l : Filter α} {φ : ℕ → α → 𝕜} {f : α → E} {a b : ℕ → E}

/-- **`q0:def:scale`.**  A sequence of eventually nonvanishing functions, each
`o` of its predecessor along `l`. -/
structure IsAsymptoticScale (l : Filter α) (φ : ℕ → α → 𝕜) : Prop where
  eventually_ne : ∀ n, ∀ᶠ x in l, φ n x ≠ 0
  isLittleO_succ : ∀ n, φ (n + 1) =o[l] φ n

/-- The finite Poincaré sum through the terms of index strictly below `N`.
The scale is scalar-valued, while the constant coefficients may lie in any
normed space over the scalar field. -/
def poincarePartialSum (φ : ℕ → α → 𝕜) (a : ℕ → E) (N : ℕ) (x : α) : E :=
  ∑ n ∈ range N, φ n x • a n

/-- The order-zero Poincaré partial sum is empty. -/
@[simp]
theorem poincarePartialSum_zero (φ : ℕ → α → 𝕜) (a : ℕ → E) (x : α) :
    poincarePartialSum φ a 0 x = 0 := by
  simp [poincarePartialSum]

/-- Increasing the truncation order appends the term at the old order. -/
theorem poincarePartialSum_succ (φ : ℕ → α → 𝕜) (a : ℕ → E) (N : ℕ) (x : α) :
    poincarePartialSum φ a (N + 1) x =
      poincarePartialSum φ a N x + φ N x • a N := by
  rw [poincarePartialSum, poincarePartialSum, Finset.sum_range_succ]

/-- **`q0:def:poincare`.**  `f ∼ ∑ aₙ φₙ` on the scale `φ`: every truncation
leaves a remainder of the order of the first omitted term. -/
def IsPoincareExpansion (l : Filter α) (φ : ℕ → α → 𝕜)
    (f : α → E) (a : ℕ → E) : Prop :=
  ∀ N, (fun x => f x - poincarePartialSum φ a N x) =O[l] φ N

/-- The `N`-th remainder of a Poincaré expansion is `o(φ_N)` once the `N`-th
term is subtracted: this is the whole content of the uniqueness argument. -/
theorem IsPoincareExpansion.isLittleO_succ_remainder
    (hs : IsAsymptoticScale l φ) (h : IsPoincareExpansion l φ f a) (N : ℕ) :
    (fun x => (f x - poincarePartialSum φ a N x) - φ N x • a N) =o[l] φ N := by
  have hO := h (N + 1)
  have hcongr : (fun x => f x - poincarePartialSum φ a (N + 1) x) =
      fun x => (f x - poincarePartialSum φ a N x) - φ N x • a N := by
    funext x
    rw [poincarePartialSum_succ]
    abel
  rw [hcongr] at hO
  exact hO.trans_isLittleO (hs.isLittleO_succ N)

/-- **`q0:eq:coefficients`.**  Each coefficient is the limit of the normalized
remainder, so it is determined by `f` and the scale.  For vector-valued
coefficients, normalization is inverse scalar multiplication. -/
theorem IsPoincareExpansion.tendsto_coeff
    (hs : IsAsymptoticScale l φ) (h : IsPoincareExpansion l φ f a) (N : ℕ) :
    Tendsto (fun x => (φ N x)⁻¹ • (f x - poincarePartialSum φ a N x))
      l (𝓝 (a N)) := by
  have hzero := (h.isLittleO_succ_remainder hs N).tendsto_inv_smul_nhds_zero
  have hsplit : ∀ᶠ x in l,
      (φ N x)⁻¹ • ((f x - poincarePartialSum φ a N x) - φ N x • a N) + a N =
        (φ N x)⁻¹ • (f x - poincarePartialSum φ a N x) := by
    filter_upwards [hs.eventually_ne N] with x hx
    rw [smul_sub, inv_smul_smul₀ hx]
    abel
  simpa only [zero_add] using (hzero.add_const (a N)).congr' hsplit

/-- In the scalar-valued case, coefficient recovery is the literal quotient
limit printed in `q0:eq:coefficients`. -/
theorem IsPoincareExpansion.tendsto_coeff_div
    {f : α → 𝕜} {a : ℕ → 𝕜}
    (hs : IsAsymptoticScale l φ) (h : IsPoincareExpansion l φ f a) (N : ℕ) :
    Tendsto (fun x => (f x - poincarePartialSum φ a N x) / φ N x)
      l (𝓝 (a N)) := by
  simpa [div_eq_inv_mul] using h.tendsto_coeff hs N

/-- **`q0:prop:uniqueness`.**  Two coefficient sequences cannot represent the
same `f` on the same scale. -/
theorem IsPoincareExpansion.coeff_unique [l.NeBot]
    (hs : IsAsymptoticScale l φ) (ha : IsPoincareExpansion l φ f a)
    (hb : IsPoincareExpansion l φ f b) : a = b := by
  funext N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      have hsum : ∀ x, poincarePartialSum φ a N x = poincarePartialSum φ b N x := by
        intro x
        unfold poincarePartialSum
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [ih n (Finset.mem_range.mp hn)]
      have hA := ha.tendsto_coeff hs N
      have hB := hb.tendsto_coeff hs N
      have hAB : (fun x => (φ N x)⁻¹ • (f x - poincarePartialSum φ a N x)) =
          fun x => (φ N x)⁻¹ • (f x - poincarePartialSum φ b N x) := by
        funext x
        rw [hsum x]
      rw [hAB] at hA
      exact tendsto_nhds_unique hA hB

end Fabius
