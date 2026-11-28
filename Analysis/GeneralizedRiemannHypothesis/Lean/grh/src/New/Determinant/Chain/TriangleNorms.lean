import Lib.General.LinearAlgebra.TensorChains

/-!
# Gram forms of chains in triangles

An abstract triangle of spaces `F i n` has arrows `a t i n : F i n → F i (n + 1)` along row `i` and
`d t i n : F i (n + 1) → F (i + 1) n` down to the next row. The map `j i` embeds `V` in `F i 0`. The
arrows depend on a parameter `t : I`. An abstract relation `M c f` between functions `c : I → ℂ` and
`f : I → ℝ`, unital and multiplicative, is read "`c` has modulus `f`". For nonzero weights, weighted
chains along a row are injective on `V`. If the constants of the squares have prescribed moduli
`L r k`, the squares obey an adjoint law and the Gram forms of the first arrows are given, then the
Gram form of a full chain and the modulus of its constant are computed by induction. In the
application `F i n` is attached to the interval `[i + 1, i + n]`, the arrow `a` adds the greatest
element, and `d` stands for the adjoint of the map that adds the least element.

## Main definitions and results

* `New.Exchange.IsTriangle`, `New.Exchange.weightedChain`: the conditions of a triangle; the
  weighted chain of a row.
* `New.Exchange.HasSquareModuli`: the moduli of the constants of the squares and the adjoint law.
* `New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero`: for nonzero weights, chains are
  injective on `V`.
* `New.Exchange.IsTriangle.exists_inner_weightedChain_eq`: for nonzero weights and under
  `HasSquareModuli`, the Gram form of a full chain is that of the product of the Gram operators
  `S t k` of the arrows `a t k 0`, times a ratio of weights and a constant of modulus `∏ L r k`.

Notions from other files:
* `New.compUpTo L j`: for linear maps `L i : M i → M (i + 1)`, the composite
  `L (j - 1) ∘ ⋯ ∘ L 0 : M 0 → M j`.
-/

/-! ## Triangles of arrows: injectivity and Gram forms of chains -/

section TriangleNorms

open ComplexInnerProductSpace Finset Module ComplexConjugate

namespace New.Exchange

variable {I V : Type}
  {F : ℕ → ℕ → Type} [∀ i n : ℕ, NormedAddCommGroup (F i n)]
  [∀ i n : ℕ, InnerProductSpace ℂ (F i n)]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (m : ℕ) (w : I → ℕ → ℕ) (M : (I → ℂ) → (I → ℝ) → Prop) (L : ℕ → ℕ → I → ℝ)
  (a : I → ∀ i n : ℕ, F i n →ₗ[ℂ] F i (n + 1))
  (d : I → ∀ i n : ℕ, F i (n + 1) →ₗ[ℂ] F (i + 1) n) (j : ∀ i : ℕ, V →ₗᵢ[ℂ] F i 0)

/-- The square at `(i, n)` commutes up to `β`: on `F i (n + 1)`, `w t n` times `a ∘ d` equals
`w t (n + 2) / conj (β t)` times `d ∘ a`. Where `β t = 0` the second scalar is `0`. -/
def SquareCommutes (i n : ℕ) (β : I → ℂ) : Prop :=
  ∀ (t : I) (y : F i (n + 1)),
    (w t n : ℂ) • a t (i + 1) n (d t i n y) =
      (w t (n + 2) / conj (β t) : ℂ) • d t i (n + 1) (a t i (n + 1) y)

/-- The adjoint law of the square at `(i, n)` with constant `κ`: every `z` in `F i (n + 2)` has an
adjoint vector `x` for `a`, and `⟪d x, y⟫ = κ t * ⟪d z, a y⟫` for all `y`. -/
def SquareAdjoint (i n : ℕ) (κ : I → ℂ) : Prop :=
  ∀ (t : I) (z : F i (n + 1 + 1)), ∃ x : F i (n + 1),
    (∀ y : F i (n + 1), ⟪a t i (n + 1) y, z⟫ = ⟪y, x⟫) ∧
    ∀ y : F (i + 1) n, ⟪d t i n x, y⟫ = κ t * ⟪d t i (n + 1) z, a t (i + 1) n y⟫

/-- A triangle of size `m` of inner product spaces `F i n` with arrows
`a t i n : F i n → F i (n + 1)` and `d t i n : F i (n + 1) → F (i + 1) n`, weights `w t n` and
isometries `j i : V → F i 0`. The squares commute up to scalars. On the copies of `V`, `a` is
adjoint to `d`, and `d ∘ a` maps each copy injectively to the next. -/
structure IsTriangle : Prop where
  /-- Each square, for `i + n + 2 ≤ m`, commutes up to a scalar function. -/
  square_commutes (i n : ℕ) (h : i + (n + 1) < m) : ∃ β : I → ℂ, SquareCommutes w a d i n β
  /-- On the copies of `V`, the first arrow `a` of row `i` is adjoint to `d`. -/
  first_adjoint (i : ℕ) (hi : i < m) (t : I) (y : V) (z : F i (0 + 1)) :
    ⟪z, a t i 0 (j i y)⟫ = ⟪d t i 0 z, j (i + 1) y⟫
  /-- `d ∘ a` maps the copy of `V` in row `i` to the copy of `V` in row `i + 1`. -/
  comp_mem_range (i : ℕ) (hi : i < m) (t : I) (y : V) :
    d t i 0 (a t i 0 (j i y)) ∈ Set.range (j (i + 1))
  /-- `d ∘ a` has trivial kernel on the copy of `V` in row `i`. -/
  eq_zero_of_first (i : ℕ) (hi : i < m) (t : I) (y : V) (hy : d t i 0 (a t i 0 (j i y)) = 0) : y = 0

/-- The moduli of the constants of the squares of a triangle of size `m`, and the adjoint law. -/
structure HasSquareModuli : Prop where
  /-- The constant `1` has modulus `1`. -/
  modulus_one : M 1 1
  /-- Moduli multiply. -/
  modulus_mul {c c' : I → ℂ} {f f' : I → ℝ} (hc : M c f) (hc' : M c' f') : M (c * c') (f * f')
  /-- The square at `(i, n)`, for `i + n + 2 ≤ m`, commutes up to a scalar function of modulus
  `L (i + 1) (i + 1 + n + 1)`. -/
  exists_modulus_commutes (i n : ℕ) (h : i + (n + 1) < m) :
    ∃ β : I → ℂ, M β (L (i + 1) (i + 1 + n + 1)) ∧ SquareCommutes w a d i n β
  /-- Each square, for `i + n + 2 ≤ m`, obeys the adjoint law with a constant of modulus `1`. -/
  square_adjoint (i n : ℕ) (h : i + (n + 1) < m) : ∃ κ : I → ℂ, M κ 1 ∧ SquareAdjoint a d i n κ

/-- The composite `F i 0 → F i n` of the first `n` arrows `a t i k` (`k < n`) of row `i`, each
multiplied by its weight `w t k`. -/
noncomputable abbrev weightedChain (t : I) (i : ℕ) : ∀ n : ℕ, F i 0 →ₗ[ℂ] F i n :=
  compUpTo fun k : ℕ ↦ (w t k : ℂ) • a t i k

lemma weightedChain_zero_apply (t : I) (i : ℕ) (y : F i 0) : weightedChain w a t i 0 y = y :=
  rfl

lemma weightedChain_succ_apply (t : I) (i n : ℕ) (y : F i 0) :
    weightedChain w a t i (n + 1) y = (w t n : ℂ) • a t i n (weightedChain w a t i n y) :=
  rfl

/-- `d` moves past the `n`-chain (the weighted composite of the first `n` arrows `a` of a row) up to
`β`: the `n`-chain of row `i + 1` after `d ∘ a` is `w t (n + 1) / (w t 1 * w t 0 * conj (β t))`
times `d` after the `(n + 1)`-chain of row `i`. Where `β t = 0` this scalar is `0`. -/
def ChainCommutes (i n : ℕ) (β : I → ℂ) : Prop :=
  ∀ (t : I) (y : F i 0),
    weightedChain w a t (i + 1) n (d t i 0 (a t i 0 y)) =
      (w t (n + 1) / (w t 1 * w t 0 * conj (β t)) : ℂ) • d t i n (weightedChain w a t i (n + 1) y)

/-- The arrow `a t i n` that follows the `n`-chain is adjoint to `d` on chains, up to `κ`:
`⟪z, a X⟫ = κ * ⟪d z, Y⟫` for all `z` and all `y` in `V`. Here `X` is the `n`-chain of row `i` at
`j i y`, and `Y` is the `n`-chain of row `i + 1` at `j (i + 1) y`. -/
def ChainAdjoint (i n : ℕ) (κ : I → ℂ) : Prop :=
  ∀ (t : I) (y : V) (z : F i (n + 1)),
    ⟪z, a t i n (weightedChain w a t i n (j i y))⟫ =
      κ t * ⟪d t i n z, weightedChain w a t (i + 1) n (j (i + 1) y)⟫

variable {m w M L a d j}

/-- Take weights `w t n`, arrows `a t i n : F i n → F i (n + 1)` along row `i` and maps
`d t i n : F i (n + 1) → F (i + 1) n` down a row, all depending on a parameter `t`. Let `X i n` be
the `n`-chain of row `i`, the weighted composite of its first `n` arrows. Suppose that for each `t`
`X (i + 1) n ∘ d ∘ a = (w (n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` on `F i 0`
(`ChainCommutes`) and `w n • a ∘ d = (w (n + 2) / conj β') • d ∘ a` on `F i (n + 1)`
(`SquareCommutes`). Then the first law holds with `n + 1` for `n` and `β * β'` for `β`. -/
lemma ChainCommutes.succ {i n : ℕ} {β β' : I → ℂ} (h_chain : ChainCommutes w a d i n β)
    (h_square : SquareCommutes w a d i n β') :
    ChainCommutes w a d i (n + 1) (β * β') := by
  intro t y
  rw [weightedChain_succ_apply, h_chain, map_smul, smul_comm (w t n : ℂ), h_square]
  rw [weightedChain_succ_apply w a t i (n + 1), map_smul, smul_smul, smul_smul, Pi.mul_apply,
    map_mul]
  congr 1
  ring

/-- Let `X i n` be the weighted composite of the first `n` arrows `a` of row `i`, applied to
`j i y`. Suppose `⟪z, a (X i n)⟫ = κ * ⟪d z, X (i + 1) n⟫` for all `y` and `z` (`ChainAdjoint`) and
that every `z` in `F i (n + 2)` has a vector `x` with `⟪a v, z⟫ = ⟪v, x⟫` and
`⟪d x, v'⟫ = κ' * ⟪d z, a v'⟫` for all `v`, `v'` (`SquareAdjoint`). Then the first law holds with
`n + 1` for `n` and `κ * κ'` for `κ`. -/
lemma ChainAdjoint.succ {i n : ℕ} {κ κ' : I → ℂ} (h_chain : ChainAdjoint w a d j i n κ)
    (h_square : SquareAdjoint a d i n κ') :
    ChainAdjoint w a d j i (n + 1) (κ * κ') := by
  -- Move the last arrow to the other side of the inner product: `x` is its adjoint vector at `z`.
  intro t y z
  obtain ⟨x, adjoint_a, adjoint_d⟩ := h_square t z
  rw [weightedChain_succ_apply, weightedChain_succ_apply]
  rw [← inner_conj_symm, adjoint_a, inner_conj_symm, inner_smul_right, h_chain, adjoint_d,
    inner_smul_right, Pi.mul_apply]
  ring

/-- For nonzero weights, `d` moves past the empty chain with constant `1`. -/
lemma chainCommutes_zero [∀ (t : I) (n : ℕ), NeZero (w t n)] (i : ℕ) :
    ChainCommutes w a d i 0 1 := by
  intro t y
  simp [weightedChain_zero_apply, weightedChain_succ_apply, NeZero.ne, ← div_div]

/-- Take a triangle of size `m` with nonzero weights (`IsTriangle`): arrows `a` along the rows and
maps `d : F i (n + 1) → F (i + 1) n` whose squares commute up to scalars, and isometries
`j i : V → F i 0`. Let `X i n` be the weighted composite of the first `n` arrows of row `i`. For
`i + n < m` there is a function `β` of the parameter with
`X (i + 1) n ∘ d ∘ a = (w (n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` on `F i 0`
(`ChainCommutes`). -/
lemma IsTriangle.exists_chainCommutes [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_tri : IsTriangle m w a d j) (i n : ℕ) (hi : i + n < m) :
    ∃ β : I → ℂ, ChainCommutes w a d i n β := by
  induction n with
  | zero => exact ⟨1, chainCommutes_zero i⟩
  | succ n ih =>
    obtain ⟨β, h_chain⟩ := ih (by lia)
    obtain ⟨β', h_square⟩ := h_tri.square_commutes i n hi
    exact ⟨β * β', h_chain.succ h_square⟩

/-- Accumulate the commuting and adjoint laws together, tracking the
modulus of the product of their witnesses. -/
private lemma IsTriangle.exists_chain_laws [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_tri : IsTriangle m w a d j) (h_moduli : HasSquareModuli m w M L a d)
    (i n : ℕ) (hi : i + n < m) :
    ∃ β κ : I → ℂ,
      M (κ * β) (∏ k ∈ Ioc (i + 1) (i + 1 + n), L (i + 1) k) ∧
      ChainCommutes w a d i n β ∧ ChainAdjoint w a d j i n κ := by
  induction n with
  | zero =>
    refine ⟨1, 1, by simpa [Ioc_self] using h_moduli.modulus_one, chainCommutes_zero i, ?_⟩
    intro t y z
    simp [weightedChain_zero_apply, h_tri.first_adjoint i hi]
  | succ n ih =>
    obtain ⟨β, κ, h_pair, h_commutes, h_adjoint⟩ := ih (by lia)
    obtain ⟨β', hβ', h_square⟩ := h_moduli.exists_modulus_commutes i n hi
    obtain ⟨κ', hκ', h_square_adjoint⟩ := h_moduli.square_adjoint i n hi
    refine ⟨β * β', κ * κ', ?_, h_commutes.succ h_square, h_adjoint.succ h_square_adjoint⟩
    rw [← add_assoc, prod_Ioc_succ_top (by lia), mul_mul_mul_comm]
    exact h_moduli.modulus_mul h_pair (by simpa only [one_mul] using h_moduli.modulus_mul hκ' hβ')

/-- Take a triangle of size `m` with nonzero weights (`IsTriangle`): spaces `F i n`, arrows `a`
along the rows and maps `d` down a row whose squares commute up to scalars, and isometries
`j i : V → F i 0` such that `d ∘ a` maps the image of `j i` injectively to that of `j (i + 1)`.
For `i + n ≤ m` and any parameter `t : I`, the weighted composite of the first `n` arrows of row
`i` is injective on the image of `V`: if it kills `j i y`, then `y = 0`. -/
lemma IsTriangle.eq_zero_of_weightedChain_eq_zero [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_tri : IsTriangle m w a d j) {t : I} (n i : ℕ) (hi : i + n ≤ m) (y : V)
    (hy : weightedChain w a t i n (j i y) = 0) :
    y = 0 := by
  induction n generalizing i y with
  | zero => rwa [weightedChain_zero_apply, map_eq_zero_iff _ (j i).injective] at hy
  | succ n ih =>
    -- Pass to row `i + 1`: the chain there kills `x`, where `j x = d (a (j y))`.
    obtain ⟨β, h_commutes⟩ := h_tri.exists_chainCommutes i n (by lia)
    obtain ⟨x, hx⟩ := h_tri.comp_mem_range i (by lia) t y
    have h_next : weightedChain w a t (i + 1) n (j (i + 1) x) = 0 := by
      rw [hx, h_commutes, hy, map_zero, smul_zero]
    have hx_zero : x = 0 := ih (i + 1) (by lia) x h_next
    exact h_tri.eq_zero_of_first i (by lia) t y (by rw [← hx, hx_zero, map_zero])

/-- Take a triangle of size `m` with nonzero weights and `V ≠ 0` (`IsTriangle`): arrows `a` along
the rows and maps `d` down a row whose squares commute up to scalars, and isometries
`j i : V → F i 0` such that `d ∘ a` maps the image of `j i` injectively to that of `j (i + 1)`. Let
`X i n` be the weighted composite of the first `n` arrows of row `i` and let `i + n < m`. If `X
(i + 1) n ∘ d ∘ a = (w (n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` on `F i 0`, then `β`
vanishes at no parameter `t : I`. -/
lemma IsTriangle.ne_zero_of_chainCommutes [∀ (t : I) (n : ℕ), NeZero (w t n)] [Nontrivial V]
    (h_tri : IsTriangle m w a d j) {i n : ℕ} (hi : i + n < m) {β : I → ℂ}
    (h_commutes : ChainCommutes w a d i n β) (t : I) :
    β t ≠ 0 := by
  intro hβ_zero
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  obtain ⟨x, hx⟩ : ∃ x : V, j (i + 1) x = d t i 0 (a t i 0 (j i y)) :=
    h_tri.comp_mem_range i (by lia) t y
  -- The scalar of `ChainCommutes` is a quotient by `0`, that is `0`: the chain of row `i + 1`
  -- kills `x`.
  have h_next : weightedChain w a t (i + 1) n (j (i + 1) x) = 0 := by
    simp [hx, h_commutes t, hβ_zero]
  have hx_zero : x = 0 := h_tri.eq_zero_of_weightedChain_eq_zero n (i + 1) (by lia) x h_next
  exact hy (h_tri.eq_zero_of_first i (by lia) t y (by rw [← hx, hx_zero, map_zero]))

/-- Take a triangle of size `m` with nonzero weights and `V ≠ 0` (`IsTriangle`): arrows `a` along
the rows and maps `d` down a row whose squares commute up to scalars, with `d ∘ a` mapping each copy
`j i` of `V` injectively to the next. If for `i + n + 2 ≤ m` the square at `(i, n)` satisfies
`w n • a ∘ d = (w (n + 2) / conj β') • d ∘ a` on `F i (n + 1)`, then `β'` has no zero, so both sides
differ by a nonzero factor. -/
lemma IsTriangle.ne_zero_of_squareCommutes [∀ (t : I) (n : ℕ), NeZero (w t n)] [Nontrivial V]
    (h_tri : IsTriangle m w a d j) {i n : ℕ} (hi : i + (n + 1) < m) {β' : I → ℂ}
    (h_square : SquareCommutes w a d i n β') (t : I) :
    β' t ≠ 0 := by
  obtain ⟨β, h_chain⟩ := h_tri.exists_chainCommutes i n (by lia)
  have h_prod : β t * β' t ≠ 0 := h_tri.ne_zero_of_chainCommutes hi (h_chain.succ h_square) t
  exact right_ne_zero_of_mul h_prod

/-- For a parameter `t : I`, the Gram form of the `(n + 1)`-chain of row `i` is expressed through
the `n`-chain of row `i + 1`. This holds for `i + n < m` in a triangle of size `m` with nonzero
weights. Let `X i n` be the weighted composite of the first `n` arrows of row `i`. Suppose `X
(i + 1) n ∘ d ∘ a = (w (n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` on `F i 0`
(`ChainCommutes`). Suppose `⟪v, a (X i n (j i y))⟫ = κ * ⟪d v, X (i + 1) n (j (i + 1) y)⟫` for all
`y`, `v` (`ChainAdjoint`). Suppose also `j (i + 1) x' = d (a (j i x))`. Then the form of the longer
chain at `(x, z)` is `κ * β * (w 0 * w 1 * w n / w (n + 1))` times the form of the shorter chain at
`(x', z)`. -/
lemma IsTriangle.inner_weightedChain_succ [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_tri : IsTriangle m w a d j) {i n : ℕ} (hi : i + n < m) {β κ : I → ℂ}
    (h_commutes : ChainCommutes w a d i n β) (h_adjoint : ChainAdjoint w a d j i n κ) {t : I}
    {x x' : V} (hx' : j (i + 1) x' = d t i 0 (a t i 0 (j i x))) (z : V) :
    ⟪weightedChain w a t i (n + 1) (j i x), weightedChain w a t i (n + 1) (j i z)⟫ =
      κ t * β t * (w t 0 * w t 1 * w t n / w t (n + 1)) *
        ⟪weightedChain w a t (i + 1) n (j (i + 1) x'),
          weightedChain w a t (i + 1) n (j (i + 1) z)⟫ := by
  rcases subsingleton_or_nontrivial V with h_trivial | h_nontrivial
  · simp [Subsingleton.elim z 0]
  have hβ := h_tri.ne_zero_of_chainCommutes hi h_commutes t
  have hw (k : ℕ) : (w t k : ℂ) ≠ 0 := NeZero.ne _
  -- Commute the chain at `x'` and apply the adjoint law to the last arrow at `z`.
  rw [hx', h_commutes t (j i x), inner_smul_left]
  rw [weightedChain_succ_apply w a t i n (j i z), inner_smul_right, h_adjoint]
  simp only [map_div₀, map_mul, map_natCast, starRingEnd_self_apply]
  field [hβ, hw 0, hw 1, hw (n + 1)]

/-- Take a triangle of size `m` with nonzero weights (`IsTriangle`): arrows `a` along the rows and
maps `d` down a row, with `a` adjoint to `d` on the isometric copies `j i` of `V`. Suppose that the
relation `M c f`, read "`c` has modulus `f`", is multiplicative, that the squares
`w n • a ∘ d = (w (n + 2) / conj β) • d ∘ a` at `(i, n)` hold with `β` of modulus
`L (i + 1) (i + n + 2)`, and that they obey the adjoint law `SquareAdjoint` with constants of
modulus `1` (`HasSquareModuli`). Let `s : U → V` be a map, `S t i` endomorphisms of `U` for the
parameters `t : I`, and `C i` functions of modulus `1`, with
`w 0 * ⟪a x, a (s y)⟫ = C i * ⟪x, s (S t i y)⟫` for each row `i < m`. For `i + n = m` the weighted
composite of the `n` arrows of row `i` has the Gram form `κ * (w 0 * w 1 ^ n / w n) * ⟪x, s (T y)⟫`,
`T = S t i ⋯ S t (m - 1)`. The modulus of `κ` is the product of the `L r k` over `i < r < k ≤ m`. -/
lemma IsTriangle.exists_inner_weightedChain_eq [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_tri : IsTriangle m w a d j) (h_moduli : HasSquareModuli m w M L a d)
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    {s : U → V} (S : I → ℕ → End ℂ U) {C : ℕ → I → ℂ} (hC : ∀ i : ℕ, M (C i) 1)
    (hS : ∀ i < m, ∀ (t : I) (x : V) (y : U),
      w t 0 * ⟪a t i 0 (j i x), a t i 0 (j i (s y))⟫ = C i t * ⟪x, s (S t i y)⟫)
    (n i : ℕ) (hi : i + n = m) :
    ∃ κ : I → ℂ,
      M κ (∏ r ∈ Ioc i m, ∏ k ∈ Ioc r m, L r k) ∧
      ∀ (t : I) (x : V) (y : U),
        ⟪weightedChain w a t i n (j i x), weightedChain w a t i n (j i (s y))⟫ =
          κ t * (w t 0 * w t 1 ^ n / w t n) * ⟪x, s (((List.range' i n).map (S t)).prod y)⟫ := by
  -- Induction on `n`, from row `i + 1` to row `i`. The Gram form of the chain of row `i` at `x` is
  -- a multiple of that of the shorter chain of row `i + 1` at `x'`, where `j x' = d (a (j x))`;
  -- pairing with `x'` is the Gram form of the first arrow.
  induction n generalizing i with
  | zero =>
    obtain rfl : i = m := hi
    exact ⟨1, by simpa [Ioc_self] using h_moduli.modulus_one, fun t x y ↦ by
      simp [weightedChain_zero_apply, NeZero.ne]⟩
  | succ n ih =>
    have hin_lt : i + n < m := by lia
    have hi_lt : i < m := by lia
    have h_end : i + 1 + n = m := by lia
    obtain ⟨κ, hκ, gram_next⟩ := ih (i + 1) h_end
    obtain ⟨β, κ', h_pair, h_commutes, h_adjoint⟩ :=
      h_tri.exists_chain_laws h_moduli i n hin_lt
    -- The squares between rows `i` and `i + 1` give the factors with `r = i + 1`.
    have h_modulus : M (κ' * β * κ * C i) (∏ r ∈ Ioc i m, ∏ k ∈ Ioc r m, L r k) := by
      rw [← prod_Ioc_consecutive _ i.le_succ hi_lt, Nat.Ioc_succ_singleton, prod_singleton]
      simpa only [h_end, mul_one] using h_moduli.modulus_mul (h_moduli.modulus_mul h_pair hκ) (hC i)
    refine ⟨κ' * β * κ * C i, h_modulus, fun t x y ↦ ?_⟩
    rw [List.range'_succ, List.map_cons, List.prod_cons, End.mul_apply]
    obtain ⟨x', hx'⟩ : ∃ x' : V, j (i + 1) x' = d t i 0 (a t i 0 (j i x)) :=
      h_tri.comp_mem_range i hi_lt t x
    set T : End ℂ U := ((List.range' (i + 1) n).map (S t)).prod
    have gram_first : ⟪x', s (T y)⟫ * w t 0 = C i t * ⟪x, s (S t i (T y))⟫ := by
      rw [mul_comm, ← (j (i + 1)).inner_map_map, hx', ← h_tri.first_adjoint i hi_lt, hS i hi_lt]
    have hw (k : ℕ) : (w t k : ℂ) ≠ 0 := NeZero.ne _
    rw [h_tri.inner_weightedChain_succ hin_lt h_commutes h_adjoint hx', gram_next,
      (eq_div_iff (hw 0)).2 gram_first]
    simp only [Pi.mul_apply]
    field [hw 0, hw n, hw (n + 1)]

end New.Exchange

end TriangleNorms
