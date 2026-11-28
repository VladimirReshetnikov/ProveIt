import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Lib.DiscreteSeries.Haar.GramFibre

/-!
# Haar measure of G₁ and the fibre measure on frames

The group `New.Shape.G₁` is the unitary group of the form `New.Shape.J₁`, of rank `r`, with basis
`e_a`, `x_i`, `z`, `e*_a`: there are `ϱ` hyperbolic pairs `e_a, e*_a`, the span `X₀` of the `x_i` is
positive definite of rank `k`, and `z` is negative. The frame is `e_0, …, e_{ϱ-1}, z`, and 𝖴⁰ is the
unipotent group `New.Shape.Form.besselU0` that fixes it. The file compares Haar measure of G₁ with
the fibre measure of the Gram map on tuples of vectors.

Notions from other files:
* `New.LeGramFibre J E m` says that the image of `m` under `g ↦ g E` is at most the fibre measure of
  the Gram map `E' ↦ E'ᴴ J E'` over the Gram matrix of `E`.
* `New.LeFibreMeasure μ ν π b l` says that `l` is at most the fibre measure `dμ / dν` of `π` over
  `b`.
* `New.volU j` is `vol U(j)`; the measure `volume` on G₁ is Haar measure, normalised through the
  compact dual, and on the unitary group H = U(X₀) it is the Haar measure of mass one.

Main results:
* `New.LeGramFibre.mconv_embedH_le`: tuples with the Gram matrix of the basis vectors outside `X₀`.
  These vectors have fixer `H = U(X₀)`; if their image under `m` is below the fibre measure, then
  `m ∗ dh` is at most `vol U(r) / (2 ^ (r - k) vol U(k))` times Haar measure of G₁.
* `New.RealPlace.lintegral_eq_unipotent_coords`: Lebesgue measure on the `ϱ`-tuples dual to
  `e_0, …, e_{ϱ-1}` and orthogonal to `z`, in coordinates given by 𝖴⁰ and the Gram matrix.
* `New.LeGramFibre.mconv_fixerHaar_le`: frames. The standard frame has fixer 𝖴⁰ H, with the measure
  `ds = New.RealPlace.fixerHaar`; if the image of the frame under `m` is below the fibre measure,
  then `m ∗ ds` is at most `vol U(r) / (2 ^ (ϱ + 1) vol U(k))` times Haar measure of G₁.

## Relation to the literature

Known result: the fibre measure of the Gram map on tuples of vectors, in terms of Haar measure of
the unitary group. The file proves the inequality that is used. Siegel, Über die analytische Theorie
der quadratischen Formen, Ann. of Math. 36 (1935).
-/

noncomputable section

namespace New.RealPlace

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator

variable {𝔰 : Shape} {n : Type} [Fintype n] [DecidableEq n]

/-- The columns of `definiteCols`, the basis vectors `x_i` of `X₀`, are orthonormal for the standard
hermitian form. -/
theorem conjTranspose_definiteCols_mul_self : 𝔰.definiteColsᴴ * 𝔰.definiteCols = 1 :=
  inclMatrix_gram_eq_one (by simp)

/-- The matrix `J₁` of the form fixes the basis vectors `x_i` of `X₀`. -/
theorem J₁_mul_definiteCols : 𝔰.J₁ * 𝔰.definiteCols = 𝔰.definiteCols := by
  simp [J₁_eq, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc,
    conjTranspose_definiteCols_mul_self,
    inclMatrix_gram_eq_zero]

/-- For `h` in the unitary group `H` of `X₀`, the element `embedH h` of `G₁` acts on the basis
vectors `x_i` of `X₀` by the matrix `h`. -/
theorem embedH_mul_definiteCols (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
    (embedH h).val.val * 𝔰.definiteCols = 𝔰.definiteCols * h.val.val := by
  simp [coe_embedH, actOnCols, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc,
    conjTranspose_definiteCols_mul_self]

/-- Let `f` be a measurable map to the unitary group `G₁` whose values all fix the tuple of
vectors given by the columns of `E`. Then almost every element for the image of `μ` under `f`
fixes this tuple. -/
theorem ae_map_mul_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → 𝔰.G₁}
    {E : Matrix 𝔰.BesselIndex n ℂ} (hf : Measurable f) (h_fix : ∀ x : X, (f x).val.val * E = E) :
    ∀ᵐ g : 𝔰.G₁ ∂μ.map f, g.val.val * E = E :=
  (ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)).2
    (.of_forall h_fix)

/-! ### Tuples whose complement is definite -/

/-- The definite case, with `k` the dimension of `X₀`. On `k`-tuples of vectors of `X₀`, the image
under `h ↦ h (x_i)` of `vol U(k) / 2 ^ k` times the Haar probability measure of `H = U(X₀)`,
embedded in `G₁` by `embedH`, is at most the fibre measure (`LeFibreMeasure`) of the Gram map
`gramCoords` over the Gram matrix of the `x_i`, the columns of `definiteCols`. Here `volU k` is
`vol U(k)`. -/
theorem leFibreMeasure_definiteCols :
    LeFibreMeasure (volume.map fun x : Matrix 𝔰.κ 𝔰.κ ℂ ↦ 𝔰.definiteCols * x) volume
      (gramCoords 𝔰.J₁) (gramCoords 𝔰.J₁ 𝔰.definiteCols)
      ((ENNReal.ofReal (volU 𝔰.k / 2 ^ 𝔰.k) • volume.map embedH).map
        fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.definiteCols) := by
  -- Transport the statement for `U(k)` along `x ↦ definiteCols * x`, which preserves Gram matrices.
  let φ : Matrix 𝔰.κ 𝔰.κ ℂ → Matrix 𝔰.BesselIndex 𝔰.κ ℂ := fun x ↦ 𝔰.definiteCols * x
  have h_gram (x : Matrix 𝔰.κ 𝔰.κ ℂ) : gramCoords 𝔰.J₁ (φ x) = gramCoords 1 x := by
    rw [gramCoords, gram_mul, Matrix.mul_assoc _ 𝔰.J₁, J₁_mul_definiteCols,
      conjTranspose_definiteCols_mul_self,
      gramCoords]
  have h_haar : LeFibreMeasure volume volume (gramCoords 𝔰.J₁ ∘ φ) (gramCoords 𝔰.J₁ (φ 1))
      ((ENNReal.ofReal (volU 𝔰.k / 2 ^ 𝔰.k) • volume).map
        fun h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦ h.val.val * (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) := by
    simpa only [LeGramFibre, Function.comp_def, h_gram] using leGramFibre_haar (J := 1)
  simpa (disch := fun_prop) only [φ, ← Measure.map_smul, Measure.map_map, Function.comp_def,
    Matrix.mul_one, embedH_mul_definiteCols] using
    h_haar.map (φ := φ) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The fibre measure on tuples with a definite complement. `G₁` is the unitary group of the
hermitian form with Gram matrix `J₁`: ϱ hyperbolic pairs, the identity on `X₀` (basis `x_i`,
`i ∈ κ`) and `h(z, z) = −1`. Let `e` enumerate the basis, indexed by `BesselIndex`, with the `x_i`
last (`indexX₀ i` is the index of `x_i`), and let `E` be the tuple of the other `r - k = 2 ϱ + 1`
basis vectors. Suppose the image of `m` under `g ↦ g E` is at most the fibre measure `dY / dT` of
the Gram map over the Gram matrix of `E` (`LeGramFibre`). Then the convolution of `m` with the Haar
probability measure of `H = U(X₀)`, embedded in `G₁` by `embedH`, is at most
`vol U(r) / (vol U(k) 2 ^ (2 ϱ + 1))` times Haar measure of `G₁`, normalised through its compact
dual. Here `inclMatrix ℂ f` has the basis vectors with indices `f j` as columns and `volU j` is
`vol U(j)`. -/
theorem _root_.New.LeGramFibre.mconv_embedH_le (e : n ⊕ 𝔰.κ ≃ 𝔰.BesselIndex)
    (he : ∀ i : 𝔰.κ, e (Sum.inr i) = 𝔰.indexX₀ i) {m : Measure 𝔰.G₁} [SFinite m]
    (hm : LeGramFibre 𝔰.J₁ (inclMatrix ℂ (e ∘ Sum.inl)) m) :
    m ∗ₘ volume.map embedH ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) • volume := by
  -- Complete `g E` to a basis by `k` vectors orthogonal to it, which is the definite case, and
  -- compare with the fibre measure on bases.
  set E : Matrix 𝔰.BesselIndex n ℂ := inclMatrix ℂ (e ∘ Sum.inl)
  set c : ℝ := volU 𝔰.k / 2 ^ 𝔰.k
  have hc : 0 < c := div_pos (volU_pos _) (by positivity)
  have hE : Eᴴ * E = 1 := inclMatrix_gram_eq_one (e.injective.comp Sum.inl_injective)
  have hXE : 𝔰.definiteColsᴴ * E = 0 := inclMatrix_gram_eq_zero fun i j ↦ by simp [← he]
  have h_orth : Eᴴ * 𝔰.J₁ * 𝔰.definiteCols = 0 := by
    simpa [Matrix.mul_assoc, J₁_mul_definiteCols] using congrArg conjTranspose hXE
  have h_linear : LeFibreMeasure volume volume (fun y : Matrix 𝔰.BesselIndex 𝔰.κ ℂ ↦ Eᴴ * 𝔰.J₁ * y)
      (Eᴴ * 𝔰.J₁ * 𝔰.definiteCols) (volume.map fun x : Matrix 𝔰.κ 𝔰.κ ℂ ↦ 𝔰.definiteCols * x) := by
    simpa only [h_orth, Matrix.mul_zero, zero_add] using leFibreMeasure_conjTranspose_mul_mul hE
      conjTranspose_definiteCols_mul_self h_orth (by simp [← card_congr e]) (0 : Matrix n 𝔰.κ ℂ)
  have h_join : joinCols e (E, 𝔰.definiteCols) = 1 := by
    rw [← LinearEquiv.eq_symm_apply, Shape.definiteCols, ← funext he]
    rfl
  have h_embed (u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) : (embedH u).val.val * E = E := by
    simp [coe_embedH, actOnCols, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hXE]
  have h_definite : LeFibreMeasure volume (volume.prod volume)
      (fun y : Matrix 𝔰.BesselIndex 𝔰.κ ℂ ↦ (Eᴴ * 𝔰.J₁ * y, gramCoords 𝔰.J₁ y))
      (Eᴴ * 𝔰.J₁ * 𝔰.definiteCols, gramCoords 𝔰.J₁ 𝔰.definiteCols)
      ((ENNReal.ofReal c • volume.map embedH).map fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.definiteCols) :=
    h_linear.trans leFibreMeasure_definiteCols (by fun_prop)
  have h_basis : LeGramFibre 𝔰.J₁ (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)
      (m ∗ₘ (ENNReal.ofReal c • volume.map embedH)) :=
    hm.append e h_join h_definite (ae_smul_measure (ae_map_mul_eq (by fun_prop) h_embed) _)
  have h_const : volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1) =
      c⁻¹ * (volU (card 𝔰.BesselIndex) / 2 ^ card 𝔰.BesselIndex) := by
    rw [show 𝔰.r = card 𝔰.BesselIndex by simp,
      show card 𝔰.BesselIndex = 2 * 𝔰.ϱ + 1 + 𝔰.k by simp +arith]
    simp [c, pow_add, field]
  calc m ∗ₘ volume.map embedH
      = ENNReal.ofReal c⁻¹ • (m ∗ₘ (ENNReal.ofReal c • volume.map embedH)) := by
        simp [mconv_smul_right, smul_smul, ← ENNReal.ofReal_mul (inv_pos.2 hc).le, hc.ne']
    _ ≤ ENNReal.ofReal c⁻¹ •
        ENNReal.ofReal (volU (card 𝔰.BesselIndex) / 2 ^ card 𝔰.BesselIndex) • volume := by
        gcongr
        exact h_basis.le_haar
    _ = _ := by rw [h_const, smul_smul, ENNReal.ofReal_mul (by positivity)]

/-! ### Coordinates adapted to the frame -/

/-- The matrix with the columns `e_0, …, e_{ϱ-1}` and `x_i`; they span the vectors orthogonal to the
frame `e_0, …, e_{ϱ-1}, z` for the form `J₁`. -/
abbrev _root_.New.Shape.freeCols (𝔰 : Shape) : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ ⊕ 𝔰.κ) ℂ :=
  fromCols 𝔰.isotropicCols 𝔰.definiteCols

/-- The columns of `frameCols`, the frame vectors `e_0, …, e_{ϱ-1}, z`, are orthonormal for the
standard hermitian form. -/
theorem conjTranspose_frameCols_mul_self : 𝔰.frameColsᴴ * 𝔰.frameCols = 1 :=
  inclMatrix_gram_eq_one (by simp [Fin.forall_fin_succ'])

/-- The columns `e_a, x_i` of `freeCols` are orthonormal for the standard hermitian form. -/
theorem conjTranspose_freeCols_mul_self : 𝔰.freeColsᴴ * 𝔰.freeCols = 1 := by
  simp [← ext_iff, inclMatrix, mul_apply, one_apply, eq_comm]

/-- The columns `e_a, x_i` of `freeCols` are orthogonal to the frame `e_0, …, e_{ϱ-1}, z` for
the form `J₁`. -/
theorem frameCols_gram_freeCols : 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.freeCols = 0 := by
  simp [← ext_iff, J₁_eq, inclMatrix, mul_apply, Fin.forall_fin_succ']

/-- The `ϱ + 1` vectors of the frame and the `ϱ + k` columns of `freeCols` are together as many as
the basis vectors. -/
theorem card_frame_add_card_free :
    card (Fin (𝔰.ϱ + 1)) + card (Fin 𝔰.ϱ ⊕ 𝔰.κ) = card 𝔰.BesselIndex := by
  simp +arith

/-- For `q = (b, s)` in `UnipotentParams`, with `b` a complex `ϱ × k` matrix and `s` a real `ϱ × ϱ`
matrix, and `u = unipotentOf q` the element of 𝖴⁰ with parameters `q`, the tuple `u (e* + e a)` is
`e* + e (skewOfReal s + a - b bᴴ / 2) - x bᴴ`, where `e`, `x`, `e*` are the matrices
`isotropicCols`, `definiteCols`, `dualCols` with columns `e_i`, `x_i`, `e*_i`, and `skewOfReal s` is
the skew-hermitian matrix with real coordinates `s`. -/
theorem unipotentOf_mul_dualCols_add (q : 𝔰.UnipotentParams) (a : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ) :
    (unipotentOf q).val.val * (𝔰.dualCols + 𝔰.isotropicCols * a) =
      𝔰.dualCols + 𝔰.isotropicCols * (skewOfReal q.2 + a - (2⁻¹ : ℂ) • (q.1 * q.1ᴴ)) +
        𝔰.definiteCols * -q.1ᴴ := by
  simp [val_unipotentOf_coe, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, inclMatrix_gram_eq_one, inclMatrix_gram_eq_zero, inclMatrix_gram_mul_eq_zero]
  abel

/-- Coordinates on the `ϱ`-tuples `e* + e a + x c`, `p = (a, c)`, which are the tuples dual to
`e_0, …, e_{ϱ-1}` and orthogonal to `z`; `e*` is `dualCols`, `e` is `isotropicCols`, and `(e, x)` is
`freeCols`. Such a tuple is `u (e* + e T / 2)` with `u = unipotentOf q` in the unipotent group 𝖴⁰
and `T = hermOfReal t` its Gram matrix, the hermitian matrix with real coordinates `t`, and
`dp = 2 ^ (-ϱ) dt dq`, where `dq = db ds` is Lebesgue measure on the pairs `q = (b, s)` of
`UnipotentParams`. -/
theorem lintegral_eq_unipotent_coords {K : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ → ℝ≥0∞}
    (hK : Measurable K) :
    ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ, K (𝔰.dualCols + 𝔰.freeCols * p) =
      (2 ^ 𝔰.ϱ)⁻¹ * ∫⁻ t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ, ∫⁻ q : 𝔰.UnipotentParams,
        K ((unipotentOf q).val.val *
          (𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • hermOfReal t))) := by
  -- With `q = (b, s)` we have `c = -bᴴ` and `a = skewOfReal s + T / 2 - b bᴴ / 2`. For fixed `b`,
  -- translate `a` and split it into its skew-hermitian and hermitian parts.
  let F (a : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ) (b : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ) : ℝ≥0∞ :=
    K (𝔰.dualCols + (𝔰.isotropicCols * a + 𝔰.definiteCols * -bᴴ))
  have := Measure.IsAddHaarMeasure.isNegInvariant_of_regular
    (volume : Measure (Matrix 𝔰.κ (Fin 𝔰.ϱ) ℂ))
  have h_rows : MeasurePreserving
      fun x : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ × Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ ↦ fromRows x.1 (-x.2ᴴ) :=
    measurePreserving_fromRows.comp ((MeasurePreserving.id volume).prod
      ((measurePreserving_neg volume).comp measurePreserving_conjTranspose))
  calc
    _ = ∫⁻ b : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ, ∫⁻ a : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ, F a b := by
      simp (disch := fun_prop) only [← h_rows.lintegral_comp, fromCols_mul_fromRows]
      exact lintegral_prod_symm' F.uncurry (by fun_prop)
    _ = ∫⁻ b : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ, (2 ^ 𝔰.ϱ)⁻¹ *
          ∫⁻ t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ, ∫⁻ s : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ,
            F (skewOfReal s + (2⁻¹ : ℂ) • hermOfReal t - (2⁻¹ : ℂ) • (b * bᴴ)) b := by
      refine lintegral_congr fun b ↦ ?_
      rw [← lintegral_sub_right_eq_self _ ((2⁻¹ : ℂ) • (b * bᴴ)),
        lintegral_eq_skewOfReal_add_hermOfReal (by fun_prop), card_fin]
    _ = _ := by
      simp (disch := first | fun_prop | simp) only [unipotentOf_mul_dualCols_add, volume_eq_prod,
        lintegral_prod, F, add_assoc, lintegral_const_mul']
      rw [lintegral_lintegral_swap (by fun_prop)]

/-! ### Frames -/

/-- The dual vectors `e*_a`, the columns of `dualCols`. On `ϱ`-tuples `y`, the image under
`u ↦ u (e*_0, …, e*_{ϱ-1})` of `2^(-ϱ)` times Haar measure `New.Shape.besselHaar₀` of the unipotent
group 𝖴⁰ is at most the fibre measure (`LeFibreMeasure`) of the map that sends `y` to its products
with the frame `e_0, …, e_{ϱ-1}, z` (columns of `frameCols`), and to the coordinates `gramCoords` of
its Gram matrix, over the image of `(e*_0, …, e*_{ϱ-1})`. -/
theorem leFibreMeasure_dualCols :
    LeFibreMeasure volume volume
      (fun y : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ ↦ (𝔰.frameColsᴴ * 𝔰.J₁ * y, gramCoords 𝔰.J₁ y))
      (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols, gramCoords 𝔰.J₁ 𝔰.dualCols)
      ((((2 : ℝ≥0∞) ^ 𝔰.ϱ)⁻¹ • 𝔰.besselHaar₀.map Subtype.val).map
        fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.dualCols) := by
  -- Fix the products with the frame, then the Gram matrix.
  have h_dual : 𝔰.J₁ * 𝔰.frameCols * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols) = 𝔰.dualCols := by
    simp [← ext_iff, J₁_eq, inclMatrix, mul_apply, one_apply, Fin.sum_univ_castSucc]
  let μ : Measure (Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ) :=
    volume.map fun p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ ↦ 𝔰.dualCols + 𝔰.freeCols * p
  have h_linear : LeFibreMeasure volume volume (𝔰.frameColsᴴ * 𝔰.J₁ * ·)
      (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols) μ := by
    simpa only [h_dual] using leFibreMeasure_conjTranspose_mul_mul conjTranspose_frameCols_mul_self
      conjTranspose_freeCols_mul_self
      frameCols_gram_freeCols card_frame_add_card_free (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols)
  let ψ (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) (q : 𝔰.UnipotentParams) :
      Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ :=
    (unipotentOf q).val.val * (𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • hermOfReal t))
  have hψ_gram (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) (q : 𝔰.UnipotentParams) :
      gramCoords 𝔰.J₁ (ψ t q) = t := by
    -- `unipotentOf q` preserves the form, and the Gram matrix of `e* + e T / 2` is `T`.
    rw [gramCoords_U_mul, gramCoords_eq_iff]
    simp [J₁_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc,
      inclMatrix_gram_eq_one, inclMatrix_gram_eq_zero, inclMatrix_gram_mul_eq_zero,
      inclMatrix_gram_mul_eq_self]
    module
  have hψ_zero (q : 𝔰.UnipotentParams) : ψ 0 q = (unipotentOf q).val.val * 𝔰.dualCols := by
    simp [ψ, hermOfReal]
  have h_base : gramCoords 𝔰.J₁ 𝔰.dualCols = 0 := by
    simpa [hψ_zero, gramCoords_U_mul] using hψ_gram 0 0
  have h_gram : LeFibreMeasure μ volume (gramCoords 𝔰.J₁) 0
      ((volume.withDensity fun _ ↦ (2 ^ 𝔰.ϱ)⁻¹).map (ψ 0)) := by
    refine .of_coordinates (w := fun _ _ ↦ (2 ^ 𝔰.ϱ)⁻¹) (by fun_prop) (by fun_prop)
      measurable_const Filter.univ_mem (fun t _ ↦ .of_forall fun q _ ↦ hψ_gram t q)
      (.of_forall fun q ↦ ⟨Continuous.continuousAt (by fun_prop), continuousAt_const⟩) fun K hK ↦ ?_
    rw [lintegral_map hK (by fun_prop), lintegral_eq_unipotent_coords hK]
    simp [lintegral_const_mul', ψ]
  simpa (disch := fun_prop) only [withDensity_const, funext hψ_zero, h_base, Shape.besselHaar₀,
    ← Measure.map_smul, Measure.map_map, Function.comp_def, volume_eq_prod]
    using h_linear.trans h_gram (by fun_prop)

/-- The measure `ds = du dh` on the fixer 𝖴⁰ H of the frame, as a measure on `G₁`: the image under
`(u, h) ↦ u h` of the Haar measure `New.Shape.besselHaar₀` on 𝖴⁰ and the Haar measure of mass one on
`H = U(X₀)`. -/
def fixerHaar (𝔰 : Shape) : Measure 𝔰.G₁ := 𝔰.besselHaar₀.map Subtype.val ∗ₘ volume.map embedH

instance : SFinite (fixerHaar 𝔰) := by
  unfold fixerHaar
  infer_instance

/-- The fibre measure on frames. If the image of `m` under `g ↦ g F`, with `F = frameCols` the frame
`e_0, …, e_{ϱ-1}, z`, is at most the Gram map's fibre measure (`LeGramFibre`), then the convolution
of `m` with the measure `fixerHaar 𝔰` on the fixer 𝖴⁰ H of the frame is at most
`vol U(r) / (vol U(k) 2 ^ (ϱ + 1))` times Haar measure of `G₁`, normalised through its compact
dual. Here `r` is the rank, `k` the dimension of `X₀`, and `volU j` is `vol U(j)`. -/
theorem _root_.New.LeGramFibre.mconv_fixerHaar_le {m : Measure 𝔰.G₁} [SFinite m]
    (hm : LeGramFibre 𝔰.J₁ 𝔰.frameCols m) :
    m ∗ₘ fixerHaar 𝔰 ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (𝔰.ϱ + 1)) • volume := by
  -- Add the dual vectors to the frame; the complement of the tuple so obtained is definite.
  let e : (Fin (𝔰.ϱ + 1) ⊕ Fin 𝔰.ϱ) ⊕ 𝔰.κ ≃ 𝔰.BesselIndex :=
    .ofBijective (Sum.elim (Sum.elim 𝔰.besselFrame eStar) 𝔰.indexX₀) <|
      (bijective_iff_injective_and_card _).2
        ⟨by simp [Function.Injective, Fin.forall_fin_succ'], by simp +arith⟩
  let ν : Measure 𝔰.G₁ := 𝔰.besselHaar₀.map Subtype.val
  have h_fix : ∀ᵐ g : 𝔰.G₁ ∂ν, g.val.val * 𝔰.frameCols = 𝔰.frameCols := by
    refine ae_map_mul_eq measurable_subtype_coe fun u ↦ ?_
    obtain ⟨q, hq⟩ := mem_besselU0_iff_unipotentOf.1 u.property
    simp [hq, val_unipotentOf_coe, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc,
      inclMatrix_gram_eq_zero, Fin.forall_fin_succ']
  have h_pairs : LeGramFibre 𝔰.J₁ (inclMatrix ℂ (e ∘ Sum.inl)) (m ∗ₘ (((2 : ℝ≥0∞) ^ 𝔰.ϱ)⁻¹ • ν)) :=
    hm.append (.refl _) (by ext i (j | j) <;> rfl) leFibreMeasure_dualCols
      (ae_smul_measure h_fix _)
  have h_const : (2 : ℝ) ^ 𝔰.ϱ * (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) =
      volU 𝔰.r / volU 𝔰.k / 2 ^ (𝔰.ϱ + 1) := by field
  calc
    _ = (2 : ℝ≥0∞) ^ 𝔰.ϱ • ((m ∗ₘ (((2 : ℝ≥0∞) ^ 𝔰.ϱ)⁻¹ • ν)) ∗ₘ volume.map embedH) := by
        simp [mconv_smul_right, mconv_smul_left, mconv_assoc, smul_smul, ENNReal.mul_inv_cancel,
          fixerHaar, ν]
    _ ≤ (2 : ℝ≥0∞) ^ 𝔰.ϱ •
        ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) • volume := by
        gcongr
        exact h_pairs.mconv_embedH_le e fun _ ↦ rfl
    _ = _ := by
        rw [← h_const, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two]
        simp [smul_smul]

end New.RealPlace

end
