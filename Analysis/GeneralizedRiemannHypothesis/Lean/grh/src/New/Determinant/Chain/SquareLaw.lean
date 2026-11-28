import New.Determinant.Exchange.MatchingPartners

/-!
# The finite square law for theta lifts: special data, matched functions and Fourier form

This is linear algebra over a finite ring `R` with a multiplicative character `χ`, behind the
commuting squares of theta lifts. A square law relates a function `L` on `a × n` matrices to a
function `L'` on `n × b` matrices. The rule for a square is the law written out for the weights `p`
and `nextDatum p`, and a second identity follows by applying the rule to a Fourier transform.

## Main definitions and results

* `New.Exchange.SquareLaw`: `L` and `L'` transform by `χ ∘ det`, and `∑ Ψ L' = c ∑ Φ L` for all
  matched functions `Φ`, `Ψ`.
* `New.Exchange.pointDatum`, `New.Exchange.nextDatum`: the point datum, which is the indicator
  function of the matrix `(1; 0)`, and the datum built from a function `p` on `n × a` matrices,
  which has the value `p (-η)`, divided by the number of blocks `s`, at `(η s; 0 1)`.
* `New.Exchange.SquareLaw.sum_eq_nextDatum`: the square law for `p` and `nextDatum p`.
* `New.Exchange.SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum`: for primitive characters and
  the shapes `n = N`, `a = N ⊕ T`, `b = T`, an identity of the same kind between the Fourier
  transforms of the weights, with a constant of known modulus in place of the group orders.

Notions from other files:
* `New.firstCols e k`, `New.invLastRows e k`: for `k` invertible and indices split by
  `e : b ⊕ a ≃ n`, the columns `b` of `k` and the rows `a` of `k⁻¹`.
* `New.AreMatched ⊤ e χ Φ Ψ`: `Φ` vanishes off the matrices `invLastRows e k`, `Ψ` vanishes off the
  matrices `firstCols e k`, and `Φ (invLastRows e k) = χ (det k) Ψ (firstCols e k)` for all `k`.
* `New.inclMatrix R u`: for a map `u : m → n` of index sets, the `n × m` matrix whose `j`-th column
  is the standard basis vector of index `u j`.
* `New.Exchange.matrixFourier ψ f`: the function `ρ ↦ ∑ v, f v * ψ (tr (ρ v))`.
* `New.Exchange.IsPrimitiveMulChar χ`: for every `a ≠ 0` some `χ (1 + c * a)` is neither `0` nor
  `1`.

## Relation to the literature

See `New.Determinant.Exchange.OneSquare` and `New.Determinant.Chain.ChainNorms` for related work.
-/

noncomputable section

section SquareLaw

open Matrix Finset Fintype Equiv Function MulChar

namespace New.Exchange

variable {R : Type} [Fintype R]
  {a b N n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype N]
  [DecidableEq N] [Fintype n] [DecidableEq n]

/-! ### The square law and the data -/

/-- The square law with constant `c` for a function `L` on `a × n` matrices and a function `L'` on
`n × b` matrices over the finite ring `R`, the indices being split by `σ : b ⊕ a ≃ n`: both
functions transform by `χ ∘ det`, and `∑ Ψ L' = c ∑ Φ L` for all matched functions `Φ`, `Ψ` in the
sense of `New.AreMatched`. In the application `L x` and `L' y` are values of the two composites of
theta lifts around a commuting square. -/
structure SquareLaw [CommRing R] (χ : MulChar R ℂ) (σ : b ⊕ a ≃ n) (c : ℂ) (L : Matrix a n R → ℂ)
    (L' : Matrix n b R → ℂ) where
  /-- `L` transforms by `χ ∘ det` under left multiplication by invertible matrices. -/
  left_mul (k : GL a R) (x : Matrix a n R) : L (k.val * x) = χ k.val.det * L x
  /-- `L'` transforms by `χ ∘ det` under right multiplication by invertible matrices. -/
  right_mul (k : GL b R) (y : Matrix n b R) : L' (y * k.val) = χ k.val.det * L' y
  /-- For matched functions `Φ`, `Ψ` the sum of `Ψ L'` is `c` times the sum of `Φ L`. -/
  sum_eq_of_areMatched (Φ : Matrix a n R → ℂ) (Ψ : Matrix n b R → ℂ) :
      AreMatched ⊤ σ χ Φ Ψ → ∑ y : Matrix n b R, Ψ y * L' y = c * ∑ x : Matrix a n R, Φ x * L x

variable (R) in
/-- The point datum: the indicator function of the inclusion matrix `(1; 0)` among the
`(a ⊕ b) × a` matrices. -/
abbrev pointDatum [CommRing R] [DecidableEq R] :
    Matrix (a ⊕ b) a R → ℂ := Pi.single (inclMatrix R Sum.inl) 1

/-- The datum built from a function `p` on `n × a` matrices. It is a function on
`(n ⊕ b) × (a ⊕ b)` matrices. At a block matrix `(η s; 0 1)`, with `η` of size `n × a` and `s` any
`n × b` matrix, its value is `p (-η)` divided by the number of all `n × b` matrices over `R`; it
vanishes at all other matrices. -/
def nextDatum [CommRing R] [DecidableEq R]
    (p : Matrix n a R → ℂ) (y : Matrix (n ⊕ b) (a ⊕ b) R) : ℂ :=
  if y.toBlocks₂₂ = 1 ∧ y.toBlocks₂₁ = 0 then p (-y.toBlocks₁₁) / Fintype.card (Matrix n b R) else 0

/-- The order of the basis of `n ⊕ a ⊕ b` that puts the block `a` first. -/
def swapFirstTwo : a ⊕ n ⊕ b ≃ n ⊕ a ⊕ b :=
  (sumAssoc a n b).symm.trans (((sumComm a n).sumCongr (Equiv.refl b)).trans (sumAssoc n a b))

/-- A sum over matrices with rows `N ⊕ n` is a double sum over the two blocks of rows. -/
lemma sum_eq_sum_fromRows (f : Matrix (N ⊕ n) a R → ℂ) :
    ∑ w : Matrix (N ⊕ n) a R, f w = ∑ y : Matrix N a R, ∑ z : Matrix n a R, f (fromRows y z) := by
  have h_bij : Bijective fun w : Matrix N a R × Matrix n a R ↦ fromRows w.1 w.2 :=
    ⟨fromRows_inj.uncurry, fun w ↦ ⟨(w.toRows₁, w.toRows₂), w.fromRows_toRows⟩⟩
  exact (h_bij.sum_comp f).symm.trans (sum_prod_type _)

/-- A sum over matrices with columns `N ⊕ n` is a double sum over the two blocks of columns. -/
lemma sum_eq_sum_fromCols (f : Matrix a (N ⊕ n) R → ℂ) :
    ∑ w : Matrix a (N ⊕ n) R, f w = ∑ z : Matrix a n R, ∑ y : Matrix a N R, f (fromCols y z) := by
  have h_bij : Bijective fun w : Matrix a N R × Matrix a n R ↦ fromCols w.1 w.2 :=
    ⟨fromCols_inj.uncurry, fun w ↦ ⟨(w.toCols₁, w.toCols₂), w.fromCols_toCols⟩⟩
  exact (h_bij.sum_comp f).symm.trans (sum_prod_type_right _)

/-- A sum over `(N ⊕ n) × (a ⊕ b)` matrices is a fourfold sum over the blocks. -/
lemma sum_eq_sum_fromBlocks (f : Matrix (N ⊕ n) (a ⊕ b) R → ℂ) :
    ∑ w : Matrix (N ⊕ n) (a ⊕ b) R, f w =
      ∑ B : Matrix N b R, ∑ A : Matrix N a R, ∑ D : Matrix n b R, ∑ C : Matrix n a R,
        f (fromBlocks A B C D) := by
  simp only [sum_eq_sum_fromRows f, sum_eq_sum_fromCols, fromRows_fromCols_eq_fromBlocks]

variable [CommRing R]

omit [Fintype R] [Fintype a] [Fintype b] in
/-- The matrix of the inclusion of `a` in `a ⊕ b` is `(1; 0)`. -/
lemma inclMatrix_inl : inclMatrix R Sum.inl = fromRows 1 (0 : Matrix b a R) := by
  ext (i | i) j <;> simp [inclMatrix, Matrix.one_apply]

/-- A sum of `F` weighted by `nextDatum p` is the sum of `F (η s; 0 1)` over all `n × a` matrices
`η` and all `n × b` matrices `s`, weighted by `p (-η)` divided by the number of `n × b` matrices. -/
lemma sum_nextDatum_mul [DecidableEq R] (p : Matrix n a R → ℂ) (F : Matrix (n ⊕ b) (a ⊕ b) R → ℂ) :
    ∑ x : Matrix (n ⊕ b) (a ⊕ b) R, nextDatum p x * F x =
      ∑ s : Matrix n b R, ∑ η : Matrix n a R,
        p (-η) / Fintype.card (Matrix n b R) * F (fromBlocks η s 0 1) := by
  have h_blocks (η : Matrix n a R) (s : Matrix n b R) (C : Matrix b a R) (D : Matrix b b R) :
      nextDatum p (fromBlocks η s C D) =
        if C = 0 then if D = 1 then p (-η) / Fintype.card (Matrix n b R) else 0 else 0 := by
    simp [nextDatum, ite_and, and_comm]
  simp [sum_eq_sum_fromBlocks, h_blocks]

omit [DecidableEq a] in
/-- Complex conjugation commutes with `nextDatum`. -/
lemma star_nextDatum [DecidableEq R] (p : Matrix n a R → ℂ) :
    star (nextDatum (b := b) p) = nextDatum (star p) :=
  funext fun y ↦ by simp [nextDatum, apply_ite star]

/-- If `f g = χ (det g) v` for all invertible `g`, the sum of `χ⁻¹ (det u) f u` over all square
matrices `u` is `v` times the order of the general linear group. -/
lemma sum_inv_det_mul_eq_card_mul [DecidableEq R] (χ : MulChar R ℂ) {f : Matrix a a R → ℂ} {v : ℂ}
    (hf : ∀ g : GL a R, f g.val = χ g.val.det * v) :
    ∑ u : Matrix a a R, χ⁻¹ u.det * f u = Fintype.card (GL a R) * v := by
  have h_ne (g : GL a R) : χ g.val.det ≠ 0 := ((isUnits_det_units g).map χ).ne_zero
  calc _ = ∑ g : GL a R, χ⁻¹ g.val.det * f g.val := by
        refine (sum_of_injective _ Units.val_injective _ _ (fun u hu ↦ ?_) fun _ ↦ rfl).symm
        rw [χ⁻¹.map_nonunit (mt u.isUnit_iff_isUnit_det.2 hu), zero_mul]
    _ = ∑ _g : GL a R, v := by simp only [hf, inv_apply_eq_inv', inv_mul_cancel_left₀ (h_ne _)]
    _ = _ := by simp

/-! ### Consequences of the square law -/

/-- The square law at a point. The hypothesis `hL` says that `L (k x) = χ (det k) L x` and
`L' (y k) = χ (det k) L' y` for invertible `k`, and that `∑ Ψ L' = c ∑ Φ L` for all matched `Φ`,
`Ψ`: they vanish off the rows `a` of `γ⁻¹`, resp. the columns `b` of `γ`, for invertible `γ`, and
there `Φ` is `χ (det γ)` times `Ψ`. Then for an `a × b` matrix `w`, the value of `L'` at `(1; -w)`
times `#GL b R` is `c` times the value of `L` at `(w 1)` times `#GL a R`; the index set `b ⊕ a` of
these two block matrices is identified with `n` by `σ`. -/
lemma SquareLaw.card_mul_apply_fromRows_eq [DecidableEq R] {χ : MulChar R ℂ} {σ : b ⊕ a ≃ n} {c : ℂ}
    {L : Matrix a n R → ℂ} {L' : Matrix n b R → ℂ} (hL : SquareLaw χ σ c L L') (w : Matrix a b R) :
    Fintype.card (GL b R) * L' ((fromRows 1 (-w)).submatrix σ.symm id) =
      c * (Fintype.card (GL a R) * L ((fromCols w 1).submatrix id σ.symm)) := by
  -- Apply the law to the matched functions `χ⁻¹(det x₂) δ(x₂⁻¹ x₁)` and `χ⁻¹(det y₁) δ(-y₂ y₁⁻¹)`,
  -- with `δ` the indicator function of `w`, and evaluate the two sums.
  let δ : Matrix a b R → ℂ := Pi.single w 1
  let rows (y₁ : Matrix b b R) (y₂ : Matrix a b R) : ℂ := L' ((fromRows y₁ y₂).submatrix σ.symm id)
  let cols (x₁ : Matrix a b R) (x₂ : Matrix a a R) : ℂ := L ((fromCols x₁ x₂).submatrix id σ.symm)
  have h_sums : ∑ y₁ : Matrix b b R, χ⁻¹ y₁.det * ∑ y₂, δ (-(y₂ * y₁⁻¹)) * rows y₁ y₂ =
      c * ∑ x₂ : Matrix a a R, χ⁻¹ x₂.det * ∑ x₁, δ (x₂⁻¹ * x₁) * cols x₁ x₂ := by
    have h_law := hL.sum_eq_of_areMatched _ _ (Rows.areMatched_block σ χ δ)
    rw [← (reindex σ (.refl b)).sum_comp, sum_eq_sum_fromRows, ← (reindex (.refl a) σ).sum_comp,
      sum_eq_sum_fromCols] at h_law
    simpa [Rows.blockRowDatum, Rows.blockColDatum, ← mul_sum, mul_assoc] using h_law
  have h_rows (g : GL b R) :
      ∑ y₂, δ (-(y₂ * (g.val)⁻¹)) * rows g.val y₂ = χ g.val.det * rows 1 (-w) :=
    calc _ = L' ((fromRows 1 (-w) * g.val).submatrix σ.symm id) := by
          simp [δ, rows, Pi.single_apply, neg_eq_iff_eq_neg, mul_inv_eq_iff_eq_mul_of_invertible]
      _ = _ := hL.right_mul g _
  have h_cols (g : GL a R) : ∑ x₁, δ ((g.val)⁻¹ * x₁) * cols x₁ g.val = χ g.val.det * cols w 1 :=
    calc _ = L ((g.val * fromCols w 1).submatrix id σ.symm) := by
          simp [δ, cols, Pi.single_apply, inv_mul_eq_iff_eq_mul_of_invertible]
      _ = _ := hL.left_mul g _
  rwa [sum_inv_det_mul_eq_card_mul χ h_rows, sum_inv_det_mul_eq_card_mul χ h_cols] at h_sums

/-- Split `n ⊕ a ⊕ b` into `a` and `n ⊕ b` (`swapFirstTwo`). Let `L`, `L'` satisfy the square law
with constant `c`: they transform by `χ ∘ det` on the left, resp. right, and `∑ Ψ L' = c ∑ Φ L`
whenever `Φ`, `Ψ` vanish off the rows `n ⊕ b` of `γ⁻¹`, resp. the columns `a` of `γ`, for invertible
`γ`, and there `Φ` is `χ (det γ)` times `Ψ`. Evaluate `L'` at `y` stacked on the inclusion matrix
`(1; 0)` of `a` in `a ⊕ b`, and `L` at the inclusion matrix of `n` in `n ⊕ b` placed left of `x`.
Then `#GL a R` times the sum of `L'` weighted by `p y` is `c` times `#GL (n ⊕ b) R` times the sum of
`L` weighted by `nextDatum p x`. -/
lemma SquareLaw.sum_eq_nextDatum [DecidableEq R] {χ : MulChar R ℂ} {c : ℂ}
    {L : Matrix (n ⊕ b) (n ⊕ a ⊕ b) R → ℂ} {L' : Matrix (n ⊕ a ⊕ b) a R → ℂ}
    (hL : SquareLaw χ (swapFirstTwo : a ⊕ n ⊕ b ≃ n ⊕ a ⊕ b) c L L') (p : Matrix n a R → ℂ) :
    Fintype.card (GL a R) * ∑ y : Matrix n a R, p y * L' (fromRows y (inclMatrix R Sum.inl)) =
      c * Fintype.card (GL (n ⊕ b) R) *
        ∑ x : Matrix (n ⊕ b) (a ⊕ b) R, nextDatum p x * L (fromCols (inclMatrix R Sum.inl) x) := by
  -- Take the law at the point `w = (η; 0)`, multiply `(w 1)` on the left by the unipotent matrix
  -- `(1 s; 0 1)`, and sum over `η` with the weights `p (-η)` and average over `s`.
  have h_shear (η : Matrix n a R) (s : Matrix n b R) :
      card (GL a R) * L' (fromRows (-η) (inclMatrix R .inl)) =
        c * (card (GL (n ⊕ b) R) * L (fromCols (inclMatrix R .inl) (fromBlocks η s 0 1))) := by
    let w : Matrix (n ⊕ b) a R := fromRows η 0
    let u : GL (n ⊕ b) R := .mk'' (fromBlocks 1 s 0 1) (by simp)
    have h_rows : fromRows (-η) (inclMatrix R .inl) =
        (fromRows 1 (-w)).submatrix (swapFirstTwo (b := b)).symm id := by
      simp [← ext_iff, w, swapFirstTwo, inclMatrix, Matrix.one_apply]
    have h_cols : fromCols (inclMatrix R .inl) (fromBlocks η s 0 1) =
        u.val * (fromCols w 1).submatrix id swapFirstTwo.symm := by
      simp [← ext_iff, u, w, swapFirstTwo, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
    have h_det : u.val.det = 1 := by simp [u]
    rw [h_rows, h_cols, hL.left_mul u, h_det, map_one, one_mul, hL.card_mul_apply_fromRows_eq w]
  rw [← neg_bijective.sum_comp, sum_nextDatum_mul, sum_comm, mul_sum, mul_sum]
  refine sum_congr rfl fun η _ ↦ ?_
  calc _ = ∑ _s : Matrix n b R, p (-η) / card (Matrix n b R) *
          (card (GL a R) * L' (fromRows (-η) (inclMatrix R .inl))) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field [Fintype.card_ne_zero]
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun s _ ↦ by
          linear_combination p (-η) / card (Matrix n b R) * h_shear η s

/-! ### The matched function of a function, and blocks of invertible matrices -/

/-- The embedding `g ↦ g ⊕ 1` of `GL b R` in `GL n R`, in the order of the basis given by `e`. -/
abbrev blockInlGL (e : b ⊕ a ≃ n) : GL b R →* GL n R :=
  (reindexGL e).toMonoidHom.comp (blockGL (R := R).comp (MonoidHom.inl (GL b R) (GL a R)))

omit [Fintype R] in
lemma blockInlGL_sumEmpty (g : GL b R) : blockInlGL (sumEmpty b Empty) g = g := by
  simp [Units.ext_iff, ← ext_iff]

/-- The function on `a × n` matrices that is `0` off the matrices `invLastRows e γ` (the rows `a`
of `γ⁻¹`) and has the value `χ (det γ) Ψ (firstCols e γ)` at `invLastRows e γ`, for a chosen `γ`.
The choice is immaterial if `Ψ` transforms by `χ⁻¹ ∘ det` on the right. -/
def matchOf (χ : MulChar R ℂ) (e : b ⊕ a ≃ n) (Ψ : Matrix n b R → ℂ) : Matrix a n R → ℂ :=
  extend (invLastRows e) (fun γ : GL n R ↦ χ γ.val.det * Ψ (firstCols e γ)) 0

variable {χ : MulChar R ℂ} {e : b ⊕ a ≃ n} {Φ Φ' : Matrix a n R → ℂ} {Ψ : Matrix n b R → ℂ}

omit [Fintype R] in
/-- If the rows `a` of `γ⁻¹` and `γ'⁻¹` agree, then the columns `b` of `γ'` are those of `γ`
multiplied on the right by an invertible `h` with `det γ' = det γ * det h`. -/
lemma exists_firstCols_eq_mul_of_invLastRows_eq {γ γ' : GL n R}
    (h_eq : invLastRows e γ = invLastRows e γ') :
    ∃ h : GL b R, firstCols e γ' = firstCols e γ * h.val ∧ γ'.val.det = γ.val.det * h.val.det := by
  have h_cols : firstCols e γ * (invFirstRows e γ * firstCols e γ') = firstCols e γ' :=
    firstCols_mul_invFirstRows_mul e γ (by rw [h_eq, invLastRows_mul_firstCols])
  have h_cols' : firstCols e γ' * (invFirstRows e γ' * firstCols e γ) = firstCols e γ :=
    firstCols_mul_invFirstRows_mul e γ' (by rw [← h_eq, invLastRows_mul_firstCols])
  let h : GL b R :=
    { val := invFirstRows e γ * firstCols e γ'
      inv := invFirstRows e γ' * firstCols e γ
      val_inv := by rw [Matrix.mul_assoc, h_cols', invFirstRows_mul_firstCols]
      inv_val := by rw [Matrix.mul_assoc, h_cols, invFirstRows_mul_firstCols] }
  refine ⟨h, h_cols.symm, ?_⟩
  let d : R := ((fromRows (invFirstRows e γ) (invLastRows e γ)).submatrix e.symm id).det
  have h_one : d * γ.val.det = 1 := by
    rw [det_fromRows_invLastRows, invFirstRows_mul_firstCols, det_one]
  have h_mixed : d * γ'.val.det = h.val.det := by simp only [d, h, h_eq, det_fromRows_invLastRows]
  linear_combination γ.val.det * h_mixed - γ'.val.det * h_one

omit [Fintype R] in
/-- If `Ψ` vanishes off the matrices `firstCols e γ` (the columns `b` of an invertible `γ`) and
satisfies `χ (det h) Ψ (y h) = Ψ y` for invertible `b × b` matrices `h`, then `Φ = matchOf χ e Ψ` is
matched with `Ψ`: it vanishes off the matrices `invLastRows e γ` (the rows `a` of `γ⁻¹`) and has
there the value `χ (det γ) Ψ (firstCols e γ)`. -/
lemma areMatched_matchOf
    (h_supp : ∀ y : Matrix n b R, Ψ y ≠ 0 → ∃ γ : GL n R, y = firstCols e γ)
    (h_right_mul : ∀ (y : Matrix n b R) (h : GL b R), χ h.val.det * Ψ (y * h.val) = Ψ y) :
    AreMatched ⊤ e χ (matchOf χ e Ψ) Ψ := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_, fun γ _ ↦ ?_⟩
  · by_contra h_off
    exact hx (extend_apply' _ _ x fun ⟨γ, hγ⟩ ↦ h_off ⟨γ, by simp [mem_intGL], hγ.symm⟩)
  · simpa [mem_intGL] using h_supp y hy
  · have h_fact : FactorsThrough (fun γ : GL n R ↦ χ γ.val.det * Ψ (firstCols e γ))
        (invLastRows e) := fun γ γ' h_eq ↦ by
      obtain ⟨h, h_cols, h_det⟩ := exists_firstCols_eq_mul_of_invLastRows_eq h_eq
      calc _ = χ γ.val.det * (χ h.val.det * Ψ (firstCols e γ * h.val)) := by rw [h_right_mul]
        _ = χ γ'.val.det * Ψ (firstCols e γ') := by rw [h_cols, h_det, map_mul, mul_assoc]
    exact h_fact.extend_apply _ γ

omit [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- If `Φ` and `Φ'` are both matched with `Ψ` (`AreMatched ⊤ e χ`), then `Φ = Φ'`. Both vanish off
the matrices `invLastRows e γ` (the rows `a` of `γ⁻¹`), for invertible `γ`. There both take the
value `χ (det γ) * Ψ (firstCols e γ)`. -/
lemma _root_.New.AreMatched.unique [DecidableEq R]
    (hΦ : AreMatched ⊤ e χ Φ Ψ) (hΦ' : AreMatched ⊤ e χ Φ' Ψ) :
    Φ = Φ' := by
  funext x
  by_cases hx : ∃ γ ∈ intGL n ⊤, x = invLastRows e γ
  · obtain ⟨γ, hγ, rfl⟩ := hx
    rw [hΦ.apply_eq γ hγ, hΦ'.apply_eq γ hγ]
  · rw [of_not_not (mt (hΦ.supp_left x) hx), of_not_not (mt (hΦ'.supp_left x) hx)]

omit [Fintype R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Let `e : b ⊕ a ≃ n` split the index set `n` into `b` and `a`, let `Φ` be a function on `a × n`
matrices and `Ψ` one on `n × b` matrices over `R`, and let `g` be invertible. Suppose that they are
matched over all of `R` (the `⊤`): they vanish off the rows `a` of `γ⁻¹`, resp. the columns `b` of
`γ`, for invertible `γ`, and there `Φ` is `χ (det γ)` times `Ψ`. Then `x ↦ c χ (det g) Φ (x g)` and
`y ↦ c Ψ (g⁻¹ y)` are matched functions. -/
lemma _root_.New.AreMatched.translate
    (h_matched : AreMatched (⊤ : Subring R) e χ Φ Ψ) (c : ℂ) (g : GL n R) :
    AreMatched (⊤ : Subring R) e χ (fun x : Matrix a n R ↦ c * χ g.val.det * Φ (x * g.val))
      fun y : Matrix n b R ↦ c * Ψ (g⁻¹.val * y) := by
  have h_rows (k γ : GL n R) : invLastRows e γ * k.val = invLastRows e (k⁻¹ * γ) := by
    simp [← ext_iff, Matrix.mul_apply]
  have h_cols (k γ : GL n R) : k.val * firstCols e γ = firstCols e (k * γ) := by
    simp [← ext_iff, Matrix.mul_apply]
  have h_mem_top (γ : GL n R) : γ ∈ intGL n (⊤ : Subring R) := by simp [mem_intGL]
  refine ⟨fun x h_ne ↦ ?_, fun y h_ne ↦ ?_, fun γ _ ↦ ?_⟩
  · obtain ⟨γ, -, hγ⟩ := h_matched.supp_left (x * g.val) (right_ne_zero_of_mul h_ne)
    exact ⟨g * γ, h_mem_top _, by simpa [← hγ] using h_rows g⁻¹ γ⟩
  · obtain ⟨γ, -, hγ⟩ := h_matched.supp_right (g⁻¹.val * y) (right_ne_zero_of_mul h_ne)
    exact ⟨g * γ, h_mem_top _, by simp [← h_cols, ← hγ]⟩
  · have h_det : γ.val.det = g.val.det * (g⁻¹ * γ).val.det := by simp [← det_mul]
    rw [h_rows, h_cols, h_matched.apply_eq _ (h_mem_top _), h_det, map_mul]
    ring

omit [Fintype N] in
/-- Let `k` be invertible. If `firstCols e k` has a left inverse `s` whose columns indexed by an
injection `f` vanish, then the columns indexed by `f` of `invLastRows e k` form a matrix with a left
inverse. -/
lemma hasLeftInv_submatrix_invLastRows (k : GL n R) {s : Matrix b n R}
    (hs : s * firstCols e k = 1) {f : N → n} (hf : Injective f) (h_zero : s.submatrix id f = 0) :
    HasLeftInv ((invLastRows e k).submatrix id f) := by
  -- The square matrix `P` with rows `s`, `invLastRows e k` has determinant inverse to `det k`. In
  -- `P⁻¹ P = 1`, read at the columns `f`, the rows `s` of `P` contribute nothing.
  let P : Matrix n n R := (fromRows s (invLastRows e k)).submatrix e.symm id
  have h_det : P.det * k.val.det = 1 := by rw [det_fromRows_invLastRows, hs, det_one]
  have h_inv : P⁻¹ * P = 1 := nonsing_inv_mul P (.of_mul_eq_one k.val.det h_det)
  have h_entry (t : b) (j : N) : s t (f j) = 0 := ext_iff.2 h_zero t j
  refine ⟨P⁻¹.submatrix f (e ∘ .inr), Matrix.ext fun i j ↦ ?_⟩
  simpa [P, Matrix.mul_apply, ← e.sum_comp, h_entry, Matrix.one_apply, hf.eq_iff]
    using ext_iff.2 h_inv (f i) (f j)

/-- Let `e` split the index set `N ⊕ n` into `b` and `a` and let `k` be invertible. Consider the
columns `b` of `k` (`firstCols e k`) and the rows `a` of `k⁻¹` (`invLastRows e k`). If the rows `N`
of the former have a left inverse, so have the columns `n` of the latter, and likewise with `N` and
`n` exchanged. -/
lemma hasLeftInv_toCols_of_hasLeftInv_toRows (e : b ⊕ a ≃ N ⊕ n) (k : GL (N ⊕ n) R) :
    (HasLeftInv (firstCols e k).toRows₁ → HasLeftInv (invLastRows e k).toCols₂) ∧
    (HasLeftInv (firstCols e k).toRows₂ → HasLeftInv (invLastRows e k).toCols₁) := by
  -- Extend the given left inverse `L` by zero to a left inverse `s` of `firstCols e k`. Stacking
  -- `s` on `invLastRows e k` gives an invertible matrix with a zero block in the rows `s`, so the
  -- columns of `invLastRows e k` under this block have a left inverse
  -- (`hasLeftInv_submatrix_invLastRows`).
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun ⟨L, hL⟩ ↦ ?_⟩
  · have h_ext : fromCols L (0 : Matrix b n R) * firstCols e k = 1 := by
      simpa [← ext_iff, Matrix.mul_apply] using hL
    have h_zero : (fromCols L (0 : Matrix b n R)).submatrix id Sum.inr = 0 := toCols₂_fromCols L 0
    exact hasLeftInv_submatrix_invLastRows k h_ext Sum.inr_injective h_zero
  · have h_ext : fromCols (0 : Matrix b N R) L * firstCols e k = 1 := by
      simpa [← ext_iff, Matrix.mul_apply] using hL
    have h_zero : (fromCols (0 : Matrix b N R) L).submatrix id Sum.inl = 0 := toCols₁_fromCols 0 L
    exact hasLeftInv_submatrix_invLastRows k h_ext Sum.inl_injective h_zero

omit [Fintype R] in
/-- Let any two elements `r`, `s` of `R` be multiples of `(1 - ε) r + ε s` for some idempotent `ε`
(the hypothesis `hR`), and let `e` split the index set `N ⊕ n` into `b` and `a`. If the rows `N` or
the rows `n` of an `(N ⊕ n) × b` matrix `y` have a left inverse, then `y` is the block
`firstCols e γ` of the columns `b` of an invertible matrix `γ`. -/
lemma exists_eq_firstCols (hR : IsValuationPair (⊤ : Subring R)) (e : b ⊕ a ≃ N ⊕ n)
    {y : Matrix (N ⊕ n) b R} (h_leftInv : HasLeftInv y.toRows₁ ∨ HasLeftInv y.toRows₂) :
    ∃ γ : GL (N ⊕ n) R, y = firstCols e γ := by
  obtain ⟨M, hM⟩ : HasLeftInv y := by
    obtain ⟨M, hM⟩ | ⟨M, hM⟩ := h_leftInv
    · exact ⟨fromCols M 0, by simpa [← ext_iff, Matrix.mul_apply] using hM⟩
    · exact ⟨fromCols 0 M, by simpa [← ext_iff, Matrix.mul_apply] using hM⟩
  have h_prim : IsPrimitiveMatrix ⊤ y := ⟨fun _ _ ↦ trivial, M, fun _ _ ↦ trivial, hM⟩
  simpa [mem_intGL] using (hR.exists_firstCols_iff e).2 h_prim

end New.Exchange

end SquareLaw

/-!
## The square law after Fourier transform

`New.Exchange.SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum` is the second of two identities
over a finite ring `R` deduced from the square law `New.Exchange.SquareLaw`. It is the first,
`New.Exchange.SquareLaw.sum_eq_nextDatum`, applied to a Fourier transform
(`New.Exchange.matrixFourier`); the Gauss sum of `χ ∘ det`
(`New.Exchange.exists_matrixFourier_eq_mul_inv_det`) gives the constant, through
`New.Exchange.exists_sum_matrixFourier_nextDatum_eq`.
-/

section SquareLawFourier

open Matrix Finset Fintype

namespace New.Exchange

/-- Let `ψ` be a primitive additive character. For a function `p` on `n × a` matrices, `nextDatum p`
is the function on `(n ⊕ b) × (a ⊕ b)` matrices that takes at each `(η s; 0 1)`, with `η` of size
`n × a` and `s` any `n × b` matrix, the value `p (-η)` divided by the number of `n × b` matrices,
and is `0` elsewhere. Its Fourier transform `ρ ↦ ∑ v, nextDatum p v * ψ (tr (ρ v))` takes at a block
matrix `(A B; C D)` the value of the transform of `p` at `-A` times `ψ (tr D)` if `C = 0`, and the
value `0` otherwise. -/
lemma matrixFourier_nextDatum_fromBlocks {R a b n : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
    {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (p : Matrix n a R → ℂ) (A : Matrix a n R)
    (B : Matrix a b R) (C : Matrix b n R) (D : Matrix b b R) :
    matrixFourier ψ (nextDatum p) (fromBlocks A B C D) =
      if C = 0 then matrixFourier ψ p (-A) * ψ D.trace else 0 := by
  have h_trace (η : Matrix n a R) (s : Matrix n b R) :
      (fromBlocks A B C D * fromBlocks η s (0 : Matrix b a R) (1 : Matrix b b R)).trace =
        (A * η).trace + (C * s).trace + D.trace := by
    simp [fromBlocks_multiply, trace, sum_add_distrib, add_assoc]
  have h_neg : ∑ η : Matrix n a R, p (-η) * ψ (A * η).trace = matrixFourier ψ p (-A) :=
    sum_bijective _ neg_bijective _ _ fun η ↦ by simp
  calc _ = ∑ s : Matrix n b R, ∑ η : Matrix n a R, p (-η) / card (Matrix n b R) *
          (ψ (A * η).trace * ψ (C * s).trace * ψ D.trace) := by
        simp only [matrixFourier, sum_nextDatum_mul, h_trace, ψ.map_add_eq_mul]
    _ = (∑ η : Matrix n a R, p (-η) * ψ (A * η).trace) * ψ D.trace *
          ((∑ s : Matrix n b R, ψ (C * s).trace) / card (Matrix n b R)) := by
        simp only [sum_div, mul_sum, sum_mul]
        exact sum_congr rfl fun s _ ↦ sum_congr rfl fun η _ ↦ by ring
    _ = _ := by simp [h_neg, sum_addChar_trace_mul hψ, ite_div]

/-- Let the additive character `ψ` and the multiplicative character `χ` of the finite ring `R` be
primitive. There is `γ`, with `‖γ‖² = #R ^ (#T (#T + 2 #N))`, such that the following holds for all
`p` and all `L` that transform by `χ ∘ det` on the left. Let `ι = inclMatrix R Sum.inl`, the
`(N ⊕ T) × N` matrix `(1; 0)` with the identity in the rows `N`, and evaluate `L` at `(ι x)`. The
sum weighted by the Fourier transform of the conjugate of `nextDatum p` is `γ` times the sum
weighted by `nextDatum` of the Fourier transform of the conjugate of `p`. -/
lemma exists_sum_matrixFourier_nextDatum_eq {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (N M T : Type) [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M] [Fintype T]
    [DecidableEq T] {χ : MulChar R ℂ} {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    (hχ : IsPrimitiveMulChar χ) :
    ∃ γ : ℂ, ‖γ‖ ^ 2 = card R ^ (card T * (card T + card N * 2)) ∧
      ∀ {L : Matrix (N ⊕ T) (N ⊕ M ⊕ T) R → ℂ} (p : Matrix M N R → ℂ),
        (∀ (k : GL (N ⊕ T) R) (x : Matrix (N ⊕ T) (N ⊕ M ⊕ T) R),
          L (k.val * x) = χ k.val.det * L x) →
        ∑ x : Matrix (N ⊕ T) (M ⊕ T) R,
            matrixFourier ψ (star (nextDatum p)) x * L (fromCols (inclMatrix R Sum.inl) x) =
          γ * ∑ x : Matrix (N ⊕ T) (M ⊕ T) R,
            nextDatum (matrixFourier ψ (star p)) x * L (fromCols (inclMatrix R Sum.inl) x) := by
  -- The first weight spreads over all corner blocks `d` with the factor `ψ (tr d)`, the second
  -- lives on `d = 1`. So `γ` is the Gauss sum `G` of `χ ∘ det` times the number of blocks `s`.
  obtain ⟨G, h_norm, h_fourier⟩ : ∃ G : ℂ, ‖G‖ ^ 2 = (card R : ℝ) ^ card T ^ 2 ∧
      ∀ S : Matrix T T R → ℂ,
        (∀ (g : GL T R) (d : Matrix T T R), S (g.val * d) = χ g.val.det * S d) →
        ∀ y : Matrix T T R, matrixFourier ψ S y = G * χ⁻¹ y.det * S 1 :=
    exists_matrixFourier_eq_mul_inv_det hψ hχ
  refine ⟨G * card (Matrix N T R), ?_, fun {L} p h_left ↦ ?_⟩
  · have h_card : card (Matrix N T R) = card R ^ (card T * card N) := by
      simp [card_congr of.symm, pow_mul]
    rw [norm_mul, mul_pow, h_norm, h_card, Complex.norm_natCast, Nat.cast_pow]
    ring
  set q : Matrix N M R → ℂ := matrixFourier ψ (star p) with hq
  let K (η : Matrix N M R) (s : Matrix N T R) (d : Matrix T T R) : ℂ :=
    L (fromCols (inclMatrix R .inl) (fromBlocks η s 0 d))
  -- Replacing the corner block `d` by `g d` multiplies `K η s d` by `χ (det g)`, so the Fourier
  -- transform of `K η s`, taken at `1`, is `G` times the value at `d = 1`.
  have h_corner (η : Matrix N M R) (s : Matrix N T R) : ∑ d, K η s d * ψ d.trace = G * K η s 1 := by
    have hK (g : GL T R) (d : Matrix T T R) : K η s (g.val * d) = χ g.val.det * K η s d := by
      let u : GL (N ⊕ T) R := blockGL (1, g)
      have h_mul : fromCols (inclMatrix R .inl) (fromBlocks η s 0 (g.val * d)) =
          u.val * fromCols (inclMatrix R .inl) (fromBlocks η s 0 d) := by
        simp [u, inclMatrix_inl, fromBlocks_mul_fromRows, fromBlocks_multiply]
      have h_det : u.val.det = g.val.det := by simp [u]
      simp only [K, h_mul, h_left u, h_det]
    simpa [matrixFourier] using h_fourier (K η s) hK 1
  calc _ = ∑ s : Matrix N T R, ∑ η : Matrix N M R, q (-η) * ∑ d, K η s d * ψ d.trace := by
        rw [star_nextDatum, sum_eq_sum_fromBlocks]
        simp [matrixFourier_nextDatum_fromBlocks hψ, ← hq, K, mul_sum, mul_assoc, mul_comm (L _)]
    _ = G * card (Matrix N T R) * ∑ s, ∑ η, q (-η) / card (Matrix N T R) * K η s 1 := by
        simp only [h_corner, mul_sum]
        exact sum_congr rfl fun s _ ↦ sum_congr rfl fun η _ ↦ by field [Fintype.card_ne_zero]
    _ = _ := by rw [sum_nextDatum_mul]

/-- Let the additive character `ψ` and the multiplicative character `χ` of the finite ring `R` be
primitive. There is `γ`, with `‖γ‖⁻² = #R ^ (#T (#T + 2 #N))`, such that the following holds for all
`p`, `c`, `L` and `L'`. Split `N ⊕ (N ⊕ T) ⊕ T` into the middle block and the two outer blocks
(`swapFirstTwo`), and assume the square law: `L`, `L'` transform by `χ ∘ det` on the left, resp.
right, and `∑ Ψ L' = c ∑ Φ L` whenever `Φ`, `Ψ` vanish off the outer rows of `k⁻¹`, resp. the middle
columns of `k`, for invertible `k`, and there `Φ` is `χ (det k)` times `Ψ`. Evaluate `L'` at `y`
stacked on the matrix `(1; 0)` of the inclusion of `N ⊕ T` in `(N ⊕ T) ⊕ T`, and `L` at that of the
inclusion of `N` in `N ⊕ T` placed left of `x`. The sum of `L'` weighted by the Fourier transform of
the conjugate of `p` is `γ c` times the sum of `L` weighted by the transform of the conjugate of
`nextDatum p`. -/
lemma SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R]
    (N T : Type) [Fintype N] [DecidableEq N] [Fintype T] [DecidableEq T] {χ : MulChar R ℂ}
    {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (hχ : IsPrimitiveMulChar χ) :
    ∃ γ : ℂ,
      -- (a) the modulus of the constant
      ‖γ‖ ^ 2 * card R ^ (card T * (card T + card N * 2)) = 1 ∧
      -- (b) the identity between the two sums
      ∀ {c : ℂ} {L : Matrix (N ⊕ T) (N ⊕ (N ⊕ T) ⊕ T) R → ℂ}
        {L' : Matrix (N ⊕ (N ⊕ T) ⊕ T) (N ⊕ T) R → ℂ} (p : Matrix (N ⊕ T) N R → ℂ),
        SquareLaw χ (swapFirstTwo (a := N ⊕ T) (b := T) (n := N)) c L L' →
        ∑ y : Matrix N (N ⊕ T) R,
            matrixFourier ψ (star p) y * L' (fromRows y (inclMatrix R Sum.inl)) =
          γ * c * ∑ x : Matrix (N ⊕ T) ((N ⊕ T) ⊕ T) R,
            matrixFourier ψ (star (nextDatum p)) x * L (fromCols (inclMatrix R Sum.inl) x) := by
  -- Apply `SquareLaw.sum_eq_nextDatum` to the Fourier transform `q` of `star p`, and pass from
  -- `nextDatum q` to the transform of `star (nextDatum p)`.
  obtain ⟨γ, h_norm, h_transform⟩ := exists_sum_matrixFourier_nextDatum_eq N (N ⊕ T) T hψ hχ
  have h_pos : 0 < ‖γ‖ ^ 2 := lt_of_lt_of_eq (by positivity) h_norm.symm
  have hγ : γ ≠ 0 := by simpa using h_pos.ne'
  refine ⟨γ⁻¹, by simp [← h_norm, hγ], fun {c L L'} p hL ↦ ?_⟩
  let q : Matrix N (N ⊕ T) R → ℂ := matrixFourier ψ (star p)
  -- The two general linear groups in the rule have the same order.
  have h_rule : ∑ y : Matrix N (N ⊕ T) R, q y * L' (fromRows y (inclMatrix R Sum.inl)) =
      c * ∑ x, nextDatum q x * L (fromCols (inclMatrix R Sum.inl) x) :=
    mul_left_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      (by linear_combination hL.sum_eq_nextDatum q)
  rw [h_rule, h_transform p hL.left_mul]
  field

end New.Exchange

end SquareLawFourier

end
