import New.UpperBound.Objects.RowChain

/-!
# Orders of block triangular groups and Gram forms of chains in triangles

The group `New.parabolic (New.blockNumber j)` consists of the invertible block upper triangular
matrices whose diagonal blocks are one copy of `N` and `j` copies of `T`. Its order is
`#GL N R * (#GL T R) ^ j` times a power of `#R` whose exponent does not depend on the commutative
ring `R`.

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

* `New.exists_card_parabolic_blockNumber_eq`: the order of the group of block triangular matrices
  `New.parabolic (New.blockNumber j)`.
* `New.Exchange.IsTriangle`, `New.Exchange.weightedChain`: the conditions of a triangle; the
  weighted chain of a row.
* `New.Exchange.HasSquareModuli`: the moduli of the constants of the squares and the adjoint law.
* `New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero`: for nonzero weights, chains are
  injective on `V`.
* `New.Exchange.IsTriangle.exists_inner_weightedChain_eq`: for nonzero weights and under
  `HasSquareModuli`, the Gram form of a full chain is that of the product of the Gram operators
  `S t k` of the arrows `a t k 0`, times a ratio of weights and a constant of modulus `∏ L r k`.

Notions from other files:
* `New.BlockIndex N T j`, `New.blockNumber j`: the disjoint union of `N` and `j` copies of `T`, and
  the number of the block of an index (`0` on `N`, and `l` on the `l`-th copy of `T`).
* `New.compUpTo L j`: for linear maps `L i : M i → M (i + 1)`, the composite
  `L (j - 1) ∘ ⋯ ∘ L 0 : M 0 → M j`.
-/

/-! ## Order of a group of block triangular matrices -/

namespace New

open Matrix Fintype

variable {N T : Type}

/-- A matrix indexed by `BlockIndex N T (j + 1) = BlockIndex N T j ⊕ T`, the union of `N` and
`j + 1` copies of `T`, is block upper triangular for the numbering `blockNumber` of the blocks
exactly when its upper left corner is block upper triangular and its lower left corner vanishes. -/
lemma blockTriangular_fromBlocks_blockNumber_succ_iff {R : Type*} [Zero R] {j : ℕ}
    {A : Matrix (BlockIndex N T j) (BlockIndex N T j) R} {B : Matrix (BlockIndex N T j) T R}
    {C : Matrix T (BlockIndex N T j) R} {D : Matrix T T R} :
    (fromBlocks A B C D).BlockTriangular (blockNumber (R := N) (T := T) (j + 1)) ↔
      A.BlockTriangular (blockNumber (R := N) (T := T) j) ∧ C = 0 := by
  refine ⟨fun h ↦ ⟨fun a b hlt ↦ h (i := .inl a) (j := .inl b) (by simpa [blockNumber] using hlt),
    Matrix.ext fun a b ↦ h (i := .inr a) (j := .inl b) (by simp [blockNumber])⟩, ?_⟩
  rintro ⟨hA, rfl⟩ (a | a) (b | b) hlt
  · exact hA (by simpa [blockNumber] using hlt)
  · simp [blockNumber, ← Fin.top_eq_last] at hlt
  · simp
  · simp [blockNumber] at hlt

variable (N T) [Fintype N] [Fintype T] [DecidableEq T] [DecidableEq N]

/-- An invertible block upper triangular matrix with blocks `N` and `j + 1` copies of `T` is a
triple: such a matrix with `j` copies of `T`, an arbitrary upper right block and an invertible last
diagonal block. Hence the orders multiply. -/
lemma card_parabolic_blockNumber_succ (R : Type*) [CommRing R] (j : ℕ) :
    Nat.card (parabolic (R := R) (blockNumber (R := N) (T := T) (j + 1))) =
      Nat.card (parabolic (R := R) (blockNumber (R := N) (T := T) j)) *
        (Nat.card (Matrix (BlockIndex N T j) T R) * Nat.card (GL T R)) := by
  let P (k : ℕ) : Subgroup (GL (BlockIndex N T k) R) := parabolic (blockNumber k)
  let mat (u : P (j + 1)) : Matrix (BlockIndex N T j ⊕ T) (BlockIndex N T j ⊕ T) R :=
    (u : GL (BlockIndex N T (j + 1)) R).val
  have h_corners (u : P (j + 1)) :
      (mat u).toBlocks₁₁.BlockTriangular (blockNumber j) ∧ (mat u).toBlocks₂₁ = 0 := by
    rw [← blockTriangular_fromBlocks_blockNumber_succ_iff, fromBlocks_toBlocks]
    exact u.property
  have h_blocks (u : P (j + 1)) :
      fromBlocks (mat u).toBlocks₁₁ (mat u).toBlocks₁₂ 0 (mat u).toBlocks₂₂ = mat u := by
    rw [← (h_corners u).right, fromBlocks_toBlocks]
  have h_unit (u : P (j + 1)) : IsUnit (mat u).toBlocks₁₁ ∧ IsUnit (mat u).toBlocks₂₂ := by
    rw [← isUnit_fromBlocks_zero₂₁, h_blocks]
    exact Units.isUnit _
  let e : P (j + 1) ≃ P j × Matrix (BlockIndex N T j) T R × GL T R :=
    { toFun u :=
        (⟨(h_unit u).left.unit, (h_corners u).left⟩, (mat u).toBlocks₁₂, (h_unit u).right.unit)
      invFun := fun (x, y, z) ↦
        ⟨(isUnit_fromBlocks_zero₂₁ (B := y).mpr ⟨x.val.isUnit, z.isUnit⟩).unit,
          blockTriangular_fromBlocks_blockNumber_succ_iff.mpr ⟨x.property, rfl⟩⟩
      left_inv u := Subtype.ext (Units.ext (h_blocks u))
      right_inv := fun (x, y, z) ↦
        Prod.ext (Subtype.ext (Units.ext rfl)) (Prod.ext rfl (Units.ext rfl)) }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]

/-- The group `parabolic (blockNumber j)` of invertible block upper triangular matrices with one
diagonal block indexed by `N` and `j` diagonal blocks indexed by `T` has order
`#GL N R * (#GL T R) ^ j * #R ^ k`, with `k` independent of the commutative ring `R`. -/
lemma exists_card_parabolic_blockNumber_eq.{u} (j : ℕ) :
    ∃ k : ℕ, ∀ (R : Type u) [CommRing R],
      Nat.card (parabolic (R := R) (blockNumber (R := N) (T := T) j)) =
        Nat.card (GL N R) * Nat.card (GL T R) ^ j * Nat.card R ^ k := by
  induction j with
  | zero =>
    refine ⟨0, fun R _ ↦ ?_⟩
    have h_top : parabolic (R := R) (blockNumber (R := N) (T := T) 0) = (⊤ : Subgroup (GL N R)) :=
      eq_top_iff.mpr fun g _ a b hlt ↦ by simp [blockNumber] at hlt
    rw [h_top, pow_zero, pow_zero, mul_one, mul_one]
    exact Subgroup.card_top
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + card (BlockIndex N T j) * card T, fun R _ ↦ ?_⟩
    have h_matrix : Nat.card (Matrix (BlockIndex N T j) T R) =
        Nat.card R ^ (card (BlockIndex N T j) * card T) := by
      simp [Matrix, Nat.card_fun, ← pow_mul, mul_comm]
    rw [card_parabolic_blockNumber_succ, hk, h_matrix]
    ring

end New

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
  set Y : F i (n + 1) := weightedChain w a t i (n + 1) y with hY
  set c : ℂ := w t (n + 1) / (w t 1 * w t 0 * conj (β t))
  calc
    weightedChain w a t (i + 1) (n + 1) (d t i 0 (a t i 0 y)) =
        c • (w t n : ℂ) • a t (i + 1) n (d t i n Y) := by
      rw [weightedChain_succ_apply, h_chain, map_smul, smul_comm]
    _ = c • (w t (n + 2) / conj (β' t) : ℂ) • d t i (n + 1) (a t i (n + 1) Y) := by rw [h_square]
    _ = (w t (n + 2) / (w t 1 * w t 0 * conj ((β * β') t)) : ℂ) •
        d t i (n + 1) (weightedChain w a t i (n + 1 + 1) y) := by
      rw [weightedChain_succ_apply, ← hY, map_smul, smul_smul, smul_smul, Pi.mul_apply, map_mul]
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
  obtain ⟨x, adjoint_a, adjoint_d⟩ : ∃ x : F i (n + 1),
      (∀ v : F i (n + 1), ⟪a t i (n + 1) v, z⟫ = ⟪v, x⟫) ∧
      ∀ v : F (i + 1) n, ⟪d t i n x, v⟫ = κ' t * ⟪d t i (n + 1) z, a t (i + 1) n v⟫ :=
    h_square t z
  rw [weightedChain_succ_apply, weightedChain_succ_apply]
  set X : F i n := weightedChain w a t i n (j i y)
  set Y : F (i + 1) n := weightedChain w a t (i + 1) n (j (i + 1) y)
  calc
    ⟪z, a t i (n + 1) ((w t n : ℂ) • a t i n X)⟫ = w t n * ⟪x, a t i n X⟫ := by
      rw [← inner_conj_symm, adjoint_a, inner_conj_symm, inner_smul_right]
    _ = w t n * (κ t * ⟪d t i n x, Y⟫) := by rw [h_chain]
    _ = (κ * κ') t * ⟪d t i (n + 1) z, (w t n : ℂ) • a t (i + 1) n Y⟫ := by
      rw [adjoint_d, inner_smul_right, Pi.mul_apply]
      ring

/-- Take a triangle of size `m` (`IsTriangle`): spaces `F i n` with arrows `a` along the rows and
maps `d : F i (n + 1) → F (i + 1) n`, such that `⟪v, a (j i y)⟫ = ⟪d v, j (i + 1) y⟫` on the
isometric copies `j i` of `V`. Read `M c f` as "the function `c` of the parameter `t : I` has
modulus `f`". Suppose that this relation is unital and multiplicative, that the squares commute up
to constants with the moduli `L`, and that every `z` at the corner of a square has a vector `x` with
`⟪a v, z⟫ = ⟪v, x⟫` and `⟪d x, v'⟫ = κ' * ⟪d z, a v'⟫`, where `M κ' 1` (`HasSquareModuli`). Then
for `i + n < m` there is `κ` with `M κ 1` and `⟪z, a (X i n)⟫ = κ * ⟪d z, X (i + 1) n⟫`
(`ChainAdjoint`), where `X i n` is the weighted composite of `n` arrows of row `i` at `j i y`. -/
lemma IsTriangle.exists_chainAdjoint (h_tri : IsTriangle m w a d j)
    (h_moduli : HasSquareModuli m w M L a d) (i n : ℕ) (hi : i + n < m) :
    ∃ κ : I → ℂ, M κ 1 ∧ ChainAdjoint w a d j i n κ := by
  induction n with
  | zero =>
    exact ⟨1, h_moduli.modulus_one, fun t y z ↦ by
      simp [weightedChain_zero_apply, h_tri.first_adjoint i hi]⟩
  | succ n ih =>
    obtain ⟨κ, hκ, h_chain⟩ := ih (by lia)
    obtain ⟨κ', hκ', h_square⟩ := h_moduli.square_adjoint i n hi
    exact ⟨κ * κ', by simpa using h_moduli.modulus_mul hκ hκ', h_chain.succ h_square⟩

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

/-- Take weights `w t n ≠ 0`, arrows `a t i n : F i n → F i (n + 1)` and maps
`d t i n : F i (n + 1) → F (i + 1) n`, with a parameter `t : I`. Suppose that the relation `M c f`,
read "`c` has modulus `f`", is unital and multiplicative and that for `i + n + 2 ≤ m` the square
`w n • a ∘ d = (w (n + 2) / conj β') • d ∘ a` on `F i (n + 1)` holds with some `β'` of modulus
`L (i + 1) (i + n + 2)` (part of `HasSquareModuli`). Let `X i n` be the weighted composite of the
first `n` arrows of row `i`. For `i + n < m` some `β` whose modulus is the product of the
`L (i + 1) k` over `i + 1 < k ≤ i + 1 + n` satisfies
`X (i + 1) n ∘ d ∘ a = (w (n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` (`ChainCommutes`). -/
lemma HasSquareModuli.exists_chainCommutes [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_moduli : HasSquareModuli m w M L a d) (i n : ℕ) (hi : i + n < m) :
    ∃ β : I → ℂ, M β (∏ k ∈ Ioc (i + 1) (i + 1 + n), L (i + 1) k) ∧ ChainCommutes w a d i n β := by
  induction n with
  | zero => exact ⟨1, by simpa [Ioc_self] using h_moduli.modulus_one, chainCommutes_zero i⟩
  | succ n ih =>
    obtain ⟨β, hβ, h_chain⟩ := ih (by lia)
    obtain ⟨β', hβ', h_square⟩ := h_moduli.exists_modulus_commutes i n hi
    refine ⟨β * β', ?_, h_chain.succ h_square⟩
    -- The product of the moduli gains the factor of the new square.
    rw [← add_assoc, prod_Ioc_succ_top (by lia)]
    exact h_moduli.modulus_mul hβ hβ'

/-- Take a triangle of size `m` with nonzero weights (`IsTriangle`): arrows `a` along the rows and
maps `d` down a row whose squares commute up to scalars, with `a` adjoint to `d` on the copies `j i`
of `V`. Let `X i n` be the weighted composite of the first `n` arrows of row `i`. For `i + n < m`
there are `β` and `κ`, functions of the parameter `t : I`, such that `X (i + 1) n ∘ d ∘ a = (w
(n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` (`ChainCommutes`). Moreover, under
`HasSquareModuli`, `κ * β` has modulus the product of the `L (i + 1) k` over `i + 1 < k ≤ i + 1 + n`
and `⟪z, a (X i n)⟫ = κ * ⟪d z, X (i + 1) n⟫` at the images of any `y` in `V` (`ChainAdjoint`). -/
lemma IsTriangle.exists_chainCommutes_and_chainAdjoint [∀ (t : I) (n : ℕ), NeZero (w t n)]
    (h_tri : IsTriangle m w a d j) (i n : ℕ) (hi : i + n < m) :
    ∃ β κ : I → ℂ,
      ChainCommutes w a d i n β ∧
      (HasSquareModuli m w M L a d →
        M (κ * β) (∏ k ∈ Ioc (i + 1) (i + 1 + n), L (i + 1) k) ∧ ChainAdjoint w a d j i n κ) := by
  by_cases h_moduli : HasSquareModuli m w M L a d
  · obtain ⟨β, hβ, h_commutes⟩ := h_moduli.exists_chainCommutes i n hi
    obtain ⟨κ, hκ, h_adjoint⟩ := h_tri.exists_chainAdjoint h_moduli i n hi
    exact ⟨β, κ, h_commutes,
      fun _ ↦ ⟨by simpa only [one_mul] using h_moduli.modulus_mul hκ hβ, h_adjoint⟩⟩
  · obtain ⟨β, h_commutes⟩ := h_tri.exists_chainCommutes i n hi
    exact ⟨β, 1, h_commutes, fun h_moduli' ↦ absurd h_moduli' h_moduli⟩

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
  have hβ : β t ≠ 0 := h_tri.ne_zero_of_chainCommutes hi h_commutes t
  set X : F i (n + 1) := weightedChain w a t i (n + 1) (j i x) with hX
  set X' : F (i + 1) n := weightedChain w a t (i + 1) n (j (i + 1) x')
  set Y : F (i + 1) n := weightedChain w a t (i + 1) n (j (i + 1) z)
  have chain_x' : X' = (w t (n + 1) / (w t 1 * w t 0 * conj (β t)) : ℂ) • d t i n X := by
    rw [hX, ← h_commutes, ← hx']
  have inner_chain_x' : ⟪X', Y⟫ = w t (n + 1) / (w t 1 * w t 0 * β t) * ⟪d t i n X, Y⟫ := by
    simp [chain_x', mul_comm]
  have hw (k : ℕ) : (w t k : ℂ) ≠ 0 := NeZero.ne _
  calc
    ⟪X, weightedChain w a t i (n + 1) (j i z)⟫ = w t n * (κ t * ⟪d t i n X, Y⟫) := by
      rw [weightedChain_succ_apply, inner_smul_right, h_adjoint]
    _ = κ t * β t * (w t 0 * w t 1 * w t n / w t (n + 1)) * ⟪X', Y⟫ := by
      rw [inner_chain_x']
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
    obtain ⟨β, hβ, h_commutes⟩ : ∃ β : I → ℂ,
        M β (∏ k ∈ Ioc (i + 1) m, L (i + 1) k) ∧ ChainCommutes w a d i n β := by
      simpa only [h_end] using h_moduli.exists_chainCommutes i n hin_lt
    obtain ⟨κ', hκ', h_adjoint⟩ := h_tri.exists_chainAdjoint h_moduli i n hin_lt
    -- The squares between rows `i` and `i + 1` give the factors with `r = i + 1`.
    have h_modulus : M (κ' * β * κ * C i) (∏ r ∈ Ioc i m, ∏ k ∈ Ioc r m, L r k) := by
      rw [← prod_Ioc_consecutive _ i.le_succ hi_lt, Nat.Ioc_succ_singleton, prod_singleton]
      simpa only [one_mul, mul_one] using
        h_moduli.modulus_mul (h_moduli.modulus_mul (h_moduli.modulus_mul hκ' hβ) hκ) (hC i)
    refine ⟨κ' * β * κ * C i, h_modulus, fun t x y ↦ ?_⟩
    rw [List.range'_succ, List.map_cons, List.prod_cons, End.mul_apply]
    obtain ⟨x', hx'⟩ : ∃ x' : V, j (i + 1) x' = d t i 0 (a t i 0 (j i x)) :=
      h_tri.comp_mem_range i hi_lt t x
    set T : End ℂ U := ((List.range' (i + 1) n).map (S t)).prod
    have gram_first : w t 0 * ⟪x', s (T y)⟫ = C i t * ⟪x, s (S t i (T y))⟫ := by
      rw [← (j (i + 1)).inner_map_map, hx', ← h_tri.first_adjoint i hi_lt, hS i hi_lt]
    have hw (k : ℕ) : (w t k : ℂ) ≠ 0 := NeZero.ne _
    calc
      ⟪weightedChain w a t i (n + 1) (j i x), weightedChain w a t i (n + 1) (j i (s y))⟫ =
          κ' t * β t * (w t 0 * w t 1 * w t n / w t (n + 1)) *
            (κ t * (w t 0 * w t 1 ^ n / w t n) * ⟪x', s (T y)⟫) := by
        rw [h_tri.inner_weightedChain_succ hin_lt h_commutes h_adjoint hx', gram_next]
      _ = κ' t * β t * κ t * (w t 0 * w t 1 ^ (n + 1) / w t (n + 1)) * (w t 0 * ⟪x', s (T y)⟫) := by
        field [hw n, hw (n + 1)]
      _ = (κ' * β * κ * C i) t * (w t 0 * w t 1 ^ (n + 1) / w t (n + 1)) *
          ⟪x, s (S t i (T y))⟫ := by
        rw [gram_first, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply]
        ring

end New.Exchange

end TriangleNorms
