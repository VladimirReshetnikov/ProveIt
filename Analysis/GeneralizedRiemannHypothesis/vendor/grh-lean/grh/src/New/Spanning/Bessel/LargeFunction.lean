import Lib.DiscreteSeries.Bessel.SchurBound
import New.Appendix.DiscreteSeries.PositionGroup
import New.Spanning.Bessel.Average
import New.Spanning.Bessel.Basic

/-!
# Bessel systems of discrete series type and a Bessel function large at a point

Given a unitary frame that diagonalises the form `New.Shape.J₁`,
`New.Filling.IsDiscreteSeriesBessel` ties an abstract Bessel system `New.BesselSystem` to a discrete
series parameter `l` and a weight `kw` of the subgroup `H = U(X₀)`. Let `𝖴` be the unipotent group
`New.Shape.Form.besselU` and let `R = 𝖴 H` be the Bessel group, realised as the subgroup
`New.Shape.besselGraph` of `G₁ × H`. There is a point `x` of bounded size at which the period of a
discrete series coefficient over `R` is large. For a parameter of large gap, the average of the
coefficient over `R` converges absolutely (`integrable_besselIntegrand`). It is a Bessel function
(`isBesselFunction_besselAverage`) that the kernel of the discrete series reproduces
(`convolve_besselAverage`).

## Main definitions and results

* `New.DiscreteSeries.UnitarySignFrame`: a unitary frame taking `J₁` to the diagonal matrix of signs
  `ε`.
* `New.Filling.IsDiscreteSeriesBessel`: the Bessel system has type `(l, kw)`.
* `New.DiscreteSeries.IsSteep.exists_stationary_point`: a point `x` of bounded length at which the
  period over `R` is large. It carries the stationary position of `U(X₀)` to the standard frame.

Notions from other files:
* `New.Shape.G₁`: the unitary group of the complex hermitian form made of ϱ hyperbolic planes, the
  standard positive form on X₀ = ℂ^κ, and one vector z with h(z, z) = −1. Its Gram matrix is
  `splitGram ϱ (middleGram κ 1)`, indexed by `New.Shape.BesselIndex`. Here n = ϱ + 1, k = |κ| and
  r is the dimension of the whole space.
* `New.Shape.besselGraph`: the Bessel group `R = 𝖴 H`, stored as the pairs of an element of G₁ and
  its image in H, with the measure `du dh`.
* `New.simpleRootSum`: the sum of the entries just above the diagonal on the frame e₁, …, e_ϱ, z.
* `New.besselLength`: for y in G₁, the infimum of ‖s y‖ + 1 over s in R; it is the length of y.
* `New.HCParam.HasLargeGap l A`: for `l = 2λ` with N coordinates, the entries are distinct, of the
  parity of N − 1, and entries of `λ` at coordinates of opposite sign are 500 N³ + A apart or more.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Periods` for related work. See
`Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure` for sources.
-/

noncomputable section

section BesselType

open Matrix MeasureTheory

/-- A fixed unitary matrix p with pᴴJ₁p the diagonal matrix of the signs ε, where
J₁ = `New.Shape.J₁`. -/
class New.DiscreteSeries.UnitarySignFrame (𝔰 : Shape)
    (ε : outParam (𝔰.BesselIndex → ℤˣ)) extends SignFrame 𝔰.J₁ ε where
  /-- The matrix `p` is unitary. -/
  mem_unitary : matrix.val ∈ unitary (Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)

/-- The Bessel system `B` has type `(l, kw)`: its full function is the Bessel function of the
discrete series of parameter `l`, with values in the representation of `H` of weight `kw`. -/
structure New.Filling.IsDiscreteSeriesBessel {𝔰 : Shape} {ε : 𝔰.BesselIndex → ℤˣ} {b : ℝ} {f : ℕ}
    [DiscreteSeries.UnitarySignFrame 𝔰 ε] (B : BesselSystem 𝔰 b f) (l : HCParam ε)
    (kw : ℕ → ℕ) where
  /-- The degree is given by Weyl's dimension polynomial at `l`. -/
  deg_eq : B.deg = weylDimensionPoly l
  /-- After an invertible change of coordinates `A`, the representation on the values is given by
  the transposed Schur matrix of weight `kw` at `gᵀ`. Here `Unit` is a set of places with one
  point. -/
  exists_conj_rep_eq_schur :
    letI V := WeylIndex 𝔰.κ fun _ : Unit ↦ kw
    ∃ (A : Matrix V B.Index ℂ) (A' : Matrix B.Index V ℂ),
      A * A' = 1 ∧
      A' * A = 1 ∧
      ∀ g : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
        A * (B.rep g).val = (schur (fun _ ↦ kw) fun _ ↦ (g : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ)ᵀ * A
  /-- The full function is fixed by right convolution with the kernel `l.dsKernel`, carried over
  from `USign ε` by the fixed frame. -/
  integral_dsKernel_mul (y : 𝔰.G₁) (i : B.Index) :
    ∫ x : USign ε, l.dsKernel x * B.besselFn .full (y * DiscreteSeries.frameEquiv.symm x) i =
      B.besselFn .full y i
  /-- The full function is `c ∫_R c_l(x⁻¹ s y) π(s)⁻¹ v ds` for a constant `c`, a point `x` and a
  vector `v`, and the integral converges absolutely. Here `c_l` is the coefficient of `l` and `π`
  is the representation of `R` that is given by `B.rep` on `H` and a character on `𝖴`. -/
  exists_eq_besselAverage : ∃ (c : ℝ) (x : 𝔰.G₁) (v : EuclideanSpace ℂ B.Index), ∀ y : 𝔰.G₁,
    Integrable (DiscreteSeries.besselIntegrand l B.rep x v y) 𝔰.besselGraphMeasure ∧
      B.besselFn .full y = c • DiscreteSeries.besselAverage l B.rep x v y

end BesselType

/-!
## The stationary point

The point `x` carries the stationary position of `H` in `G₁` to the standard frame, by Witt's
theorem.
-/

namespace New

open Matrix Complex Norms.L2Operator ComplexConjugate Finset Fin RealPlace Filling
  IsHermitianInvolution MeasureTheory Subgroup

namespace DiscreteSeries

variable {𝔰 : Shape} {ε : 𝔰.BesselIndex → ℤˣ}

/-- The measure on `R` unfolds 𝖴∖G₁ to G₁: for measurable `f ≥ 0`, the integral of `f (x s y)` over
`s` in `R` and then over `y` in G₁ for `besselQuotMeasure`, which computes integrals over 𝖴∖G₁,
is the integral of `f` over G₁. -/
lemma lintegral_unfold_besselGraphMeasure {x : 𝔰.G₁} (f : 𝔰.G₁ → ENNReal) (hf : Measurable f) :
    ∫⁻ g : 𝔰.G₁, f g = ∫⁻ y : 𝔰.G₁, ∫⁻ s : 𝔰.besselGraph,
      f (x * (s.val.fst * y)) ∂𝔰.besselGraphMeasure ∂besselQuotMeasure := by
  -- Write `s = k * u` with `k` in `H` and `u` in `𝖴`. The integrals over `u` and `y` unfold to one
  -- over the whole group, where left invariance removes `x * k`; and `H` has total mass `1`.
  have h_orbit :
      ∫⁻ y : 𝔰.G₁, ∫⁻ u : (𝔰.middleGram (1 : ℂ)).besselU, ∫⁻ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
          f (x * (embedH k * (u.val * y))) ∂volume ∂𝔰.besselHaar ∂besselQuotMeasure =
        ∫⁻ g : 𝔰.G₁, ∫⁻ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), f (x * (embedH k * g)) :=
    lintegral_orbitMeasure_lintegral
      (f := fun g : 𝔰.G₁ ↦ ∫⁻ k, f (x * (embedH k * g))) (by fun_prop)
  simp (disch := fun_prop) only [Shape.besselGraphMeasure, lintegral_map, lintegral_prod,
    Shape.besselGraphChart_apply_coe, mul_assoc]
  rw [h_orbit, lintegral_lintegral_swap (by fun_prop)]
  simp [← mul_assoc, lintegral_mul_left_eq_self]

/-- For `s` in `besselGraph` (the group `R`), its first component `s.val.fst` lowers the flag of the
frame `e₁, …, e_ϱ, z`: `(s.val.fst - 1) * frameCols = isotropicCols * N` for some strictly
triangular `N`. Here `frameCols` has columns `e₁, …, e_ϱ, z` and `isotropicCols` has columns
`e₁, …, e_ϱ`. The sum of the entries `N a a.succ` is `simpleRootSum s.val.fst`. -/
lemma exists_sub_one_mul_frameCols_eq (s : 𝔰.besselGraph) :
    ∃ N : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) ℂ,
      (∀ (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)), b.val ≤ a.val → N a b = 0) ∧
      ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) * 𝔰.frameCols =
        𝔰.isotropicCols * N ∧
      ∑ a : Fin 𝔰.ϱ, N a a.succ = simpleRootSum s.val.fst := by
  -- Write `s = h u` with `u` in `𝖴`; the factor `h` fixes the frame, and `u` is unitriangular
  -- on it.
  obtain ⟨⟨⟨u, hu⟩, h⟩, rfl⟩ := 𝔰.besselGraphChart.surjective s
  refine ⟨(frameMatrix u - 1).submatrix castSucc id,
    fun a b hab ↦ sub_eq_zero.2 (frameMatrix_unitriangular hu _ _ hab), ?_, ?_⟩
  · simp [← Matrix.ext_iff, mul_apply, apply_inr_of_mem_besselU hu, frameMatrix, inclMatrix,
      val_toBesselH_apply_coe, forall_fin_succ', Matrix.one_apply]
  · simp [mul_apply, simpleRootSum, frameMatrix, val_toBesselH_apply_coe, Matrix.one_apply,
      ne_of_lt]

/-- An element `s` of `besselGraph` (the group `R`) acts on `X₀`, the span of the columns of
`definiteCols`, by its image `s.val.snd` in `H`, modulo the span of `e₁, …, e_ϱ` (the columns of
`isotropicCols`). -/
lemma exists_sub_one_mul_definiteCols_eq (s : 𝔰.besselGraph) :
    ∃ C : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ,
      ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) * 𝔰.definiteCols =
        𝔰.definiteCols * ((s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) - 1) + 𝔰.isotropicCols * C := by
  -- Write `s = h u`; the matrix `C` is the block of `u` from `X₀` to `e₁, …, e_ϱ`.
  obtain ⟨⟨⟨u, hu⟩, h⟩, rfl⟩ := 𝔰.besselGraphChart.surjective s
  use (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ).submatrix Sum.inl 𝔰.indexX₀
  simp [← Matrix.ext_iff, mul_apply, apply_inr_of_mem_besselU hu, inclMatrix,
    val_toBesselH_apply_coe, Matrix.one_apply]

/-- Let `g` in `G₁` lower the flag of the frame `e₁, …, e_ϱ, z`. That is, `g - 1` maps the frame
into the span of `e₁, …, e_ϱ` by a strictly triangular matrix `N`. Then `g` is the first component
`s.val.fst` of some `s` in `besselGraph` (the group `R`). -/
lemma exists_besselGraph_fst_eq {g : 𝔰.G₁} {N : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) ℂ}
    (hN_tri : ∀ (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)), b.val ≤ a.val → N a b = 0)
    (hN : ((g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) * 𝔰.frameCols = 𝔰.isotropicCols * N) :
    ∃ s : 𝔰.besselGraph, s.val.fst = g := by
  have h_mem : g ∈ besselS := by
    refine mem_besselS_iff_frameImage.2 fun i b hb ↦ sub_eq_zero.1 ?_
    have h_entry : (𝔰.isotropicCols * N) i b = 0 := by
      rcases i with a | i
      · simpa [inclMatrix, mul_apply, Matrix.one_apply] using hN_tri a b hb
      · simp [inclMatrix, mul_apply]
    rwa [← hN, mul_inclMatrix] at h_entry
  obtain ⟨u, hu, h, rfl⟩ := exists_besselU_mul_toBesselH h_mem isUnit_one
  exact ⟨⟨(u * embedH h, h), by simpa [Shape.mem_besselGraph_iff_mul_inv_mem] using hu⟩, rfl⟩

variable [p : UnitarySignFrame 𝔰 ε]

/-- The map `s ↦ (x⁻¹ s x, h)`, where `h` is the image of `s` in `H` and `x⁻¹ s x` is written in the
frame of signs `ε`. -/
def besselPairHom (x : 𝔰.G₁) : 𝔰.besselGraph →* USign ε × USign (1 : 𝔰.κ → ℤˣ) :=
  .domRestrict (.prodMap (.comp (frameEquiv (ε := ε)) (MulAut.conj x⁻¹).toMonoidHom)
    (inclusion (by simp [USign]))) 𝔰.besselGraph

/-- The first component `s ↦ x⁻¹ s x` of `besselPairHom x` is proper: `R` is closed in `G₁ × H` and
`H` is compact. -/
lemma isProperMap_besselPairHom_fst (x : 𝔰.G₁) :
    IsProperMap fun s : 𝔰.besselGraph ↦ (besselPairHom (ε := ε) x s).fst := by
  exact ((Homeomorph.smul (x⁻¹ : ConjAct 𝔰.G₁)).trans frameEquiv.toHomeomorph).isProperMap.comp
    (isProperMap_fst_of_compactSpace.restrict inferInstance)

/-- The first entry of `subOnePair (besselPairHom x) s`, the first component minus one, is the
conjugate of `s - 1` by `x p`, where `p` is the frame of signs `ε`. -/
lemma subOnePair_besselPairHom_fst (s : 𝔰.besselGraph) (x : 𝔰.G₁) :
    (subOnePair (besselPairHom x) s).fst =
      (x.val * p.matrix)⁻¹.val * ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) *
        (x.val * p.matrix).val := by
  simp [besselPairHom, frameEquiv, U.conj, mul_sub, sub_mul, mul_assoc]

/-- The second component of `besselPairHom x s` has the matrix of the image of `s` in `H`. -/
lemma besselPairHom_snd_val (s : 𝔰.besselGraph) (x : 𝔰.G₁) :
    ((besselPairHom (ε := ε) x s).snd : Matrix 𝔰.κ 𝔰.κ ℂ) = (s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) := by
  simp [besselPairHom]

/-- The second entry of `subOnePair (besselPairHom x) s` is the image of `s` in `H`, minus one. -/
lemma subOnePair_besselPairHom_snd (s : 𝔰.besselGraph) (x : 𝔰.G₁) :
    (subOnePair (besselPairHom (ε := ε) x) s).snd = (s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) - 1 := by
  simp [besselPairHom_snd_val]

variable {v : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ} {i₀ : Matrix 𝔰.BesselIndex 𝔰.κ ℂ}

/-- The unitary frame `p` takes a vector with entries of modulus at most `M` to one of length at
most `√r M`, where `r` is the dimension. -/
lemma norm_frame_mulVec_le {M : ℝ} (hM : 0 ≤ M) {w : 𝔰.BesselIndex → ℂ}
    (hw : ∀ i : 𝔰.BesselIndex, ‖w i‖ ≤ M) :
    ‖WithLp.toLp 2 (p.matrix.val *ᵥ w)‖ ≤ √𝔰.r * M := by
  have h_sum : ∑ i : 𝔰.BesselIndex, ‖w i‖ ^ 2 ≤ 𝔰.r * M ^ 2 := by
    simpa using sum_le_card_nsmul univ _ _ fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
  refine (l2_opNorm_mulVec p.matrix.val (WithLp.toLp 2 w)).trans ?_
  grw [CStarRing.norm_of_mem_unitary p.mem_unitary, one_mul, EuclideanSpace.norm_eq, h_sum,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

/-- Take a position (`IsPosition`) of `H = U(X₀)` in `U(ε)`: independent vectors `v₁, …, v_n` (the
columns of `v`) whose products for the form `signMatrix ε` vanish except that of `v_n` with itself,
and an isometry `i₀` of `X₀` into their orthogonal complement. Let `v_n` have norm `-1`. Let
`w 0 = v₁, …, w (n - 1) = v_n` continue to a sequence such that `w 0, …, w (2 n - 2)` have entries
of modulus at most `M ≥ 1`, and the product of `w a` and `w b` is `0` for `a + b < 2 n - 2` and `-1`
for `a + b = 2 n - 2`. Then there is an `x` in `G₁` such that `x p`, where `p` is the frame of signs
`ε`, takes `i₀` to the inclusion of `X₀` and `v₁, …, v_n` to `e₁, …, e_ϱ, z`, and such that
`besselLength x`, the infimum of `‖s x‖ + 1` over `s` in the Bessel group, is at most `8 n √r M`. -/
lemma IsPosition.exists_mul_eq_frameCols_and_besselLength_le (hP : IsPosition ε 1 𝔰.ϱ v i₀)
    (h_norm : (vᴴ * signMatrix ε * v) (last 𝔰.ϱ) (last 𝔰.ϱ) = -1) {M : ℝ} (hM : 1 ≤ M)
    {w : ℕ → 𝔰.BesselIndex → ℂ} (hw : ∀ a : Fin (𝔰.ϱ + 1), w a = v.col a)
    (hw_le : ∀ a ≤ 2 * 𝔰.ϱ, ∀ i : 𝔰.BesselIndex, ‖w a i‖ ≤ M)
    (hw_dual : ∀ a b : ℕ, a + b ≤ 2 * 𝔰.ϱ →
      star (w a) ⬝ᵥ signMatrix ε *ᵥ w b = if a + b = 2 * 𝔰.ϱ then -1 else 0) :
    ∃ x : 𝔰.G₁,
      (x.val * p.matrix).val * i₀ = 𝔰.definiteCols ∧
      (x.val * p.matrix).val * v = 𝔰.frameCols ∧
      besselLength x ≤ 8 * 𝔰.n * (√𝔰.r * M) := by
  -- The columns of `i₀` and `v₁, …, v_n` have the Gram matrix of the basis of `X₀` and the frame.
  have h_entry (a b : Fin (𝔰.ϱ + 1)) :
      (vᴴ * signMatrix ε * v) a b = if a = last 𝔰.ϱ ∧ b = last 𝔰.ϱ then -1 else 0 := by
    split_ifs with hab
    · rw [hab.1, hab.2, h_norm]
    · exact hP.gram_eq_zero a b (not_and_or.1 hab)
  have h_frame : vᴴ * signMatrix ε * v = 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols := by
    simp_rw [← Matrix.ext_iff, h_entry]
    simp [mul_apply, inclMatrix, splitGram, middleGram, forall_fin_succ', Matrix.one_apply]
  have h_gram : (p.matrix.val * fromCols i₀ v)ᴴ * 𝔰.J₁ * (p.matrix.val * fromCols i₀ v) =
      (fromCols 𝔰.definiteCols 𝔰.frameCols)ᴴ * 𝔰.J₁ * fromCols 𝔰.definiteCols 𝔰.frameCols := by
    rw [gram_mul, p.gram_eq]
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, mul_fromCols]
    rw [hP.isometry, hP.orthogonal, hP.vec_orthogonal, h_frame]
    simp [← Matrix.ext_iff, mul_apply, inclMatrix, splitGram, middleGram, forall_fin_succ',
      Matrix.one_apply]
  -- Both families are independent, so Witt's theorem gives `x`.
  have h_indep : HasLeftInv (p.matrix.val * fromCols i₀ v) := by
    obtain ⟨Z, hZ⟩ := hP.hasLeftInv
    exact ⟨Z * p.matrix⁻¹.val, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ p.matrix.val, Units.inv_mul, Matrix.one_mul, hZ]⟩
  have h_indep' : HasLeftInv (fromCols 𝔰.definiteCols 𝔰.frameCols) :=
    ⟨(fromCols 𝔰.definiteCols 𝔰.frameCols)ᴴ, by
      simp [← Matrix.ext_iff, mul_apply, inclMatrix, Matrix.one_apply, forall_fin_succ', eq_comm]⟩
  obtain ⟨x, hx⟩ : ∃ x : 𝔰.G₁,
      x.val.val * (p.matrix.val * fromCols i₀ v) = fromCols 𝔰.definiteCols 𝔰.frameCols :=
    witt ⟨Complex.I, by simp⟩ isHermitian.eq IsHermitianInvolution.isUnit h_indep h_indep' h_gram
  rw [← Matrix.mul_assoc, ← Units.val_mul, mul_fromCols, fromCols_ext_iff] at hx
  obtain ⟨hx_isometry, hx_frame⟩ := hx
  refine ⟨x, hx_isometry, hx_frame, ?_⟩
  -- For `a ≤ 2 n - 2` the vectors `p (w a)` have length at most `√r M`, and their products for
  -- `J₁` are those of the `w a` for `signMatrix ε`.
  have h_vec (a : Fin (𝔰.ϱ + 1)) : frameVector x a = WithLp.toLp 2 (p.matrix.val *ᵥ w a) := by
    have h_inv : x⁻¹.val.val * 𝔰.frameCols = p.matrix.val * v := by
      simp [← hx_frame, ← Matrix.mul_assoc]
    ext i
    rw [hw]
    exact (congrFun₂ (mul_inclMatrix x⁻¹.val.val 𝔰.besselFrame) i a).symm.trans
      (congrFun₂ h_inv i a)
  have h_form (a b : ℕ) (hab : a + b ≤ 2 * 𝔰.ϱ) :
      star (p.matrix.val *ᵥ w a) ⬝ᵥ 𝔰.J₁ *ᵥ (p.matrix.val *ᵥ w b) =
        if a + b = 2 * 𝔰.ϱ then -1 else 0 := by
    rw [← hw_dual a b hab, ← p.gram_eq, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec (star (w a)), ← star_mulVec]
  have h_rank : 1 ≤ √(𝔰.r : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  exact_mod_cast besselLength_le_of_dual x (one_le_mul_of_one_le_of_one_le h_rank hM)
    (fun a : ℕ ↦ WithLp.toLp 2 (p.matrix.val *ᵥ w a)) h_vec
    (fun a ha ↦ norm_frame_mulVec_le (zero_le_one.trans hM) (hw_le a ha))
    fun a b hab ↦ (dotProduct_comm _ _).trans (h_form a b hab)

section Point

variable {x : 𝔰.G₁}

/-- If `x p` takes the columns of `v` to the frame, then its first ϱ columns `initCols v` are the
images of `e₁, …, e_ϱ`, the columns of `isotropicCols`, under the inverse of `x p`. -/
lemma initCols_eq_of_frame (h_frame : (x.val * p.matrix).val * v = 𝔰.frameCols) :
    initCols v = (x.val * p.matrix)⁻¹.val * 𝔰.isotropicCols := by
  have h_isotropic : (x.val * p.matrix).val * initCols v = 𝔰.isotropicCols := by
    ext i a
    calc ((x.val * p.matrix).val * initCols v) i a
      _ = ((x.val * p.matrix).val * v) i a.castSucc := rfl
      _ = 𝔰.frameCols i a.castSucc := congrFun₂ h_frame i a.castSucc
      _ = 𝔰.isotropicCols i a := by simp [inclMatrix, Matrix.one_apply]
  rw [← h_isotropic, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- At a point `x` such that `x p` sends the columns `v₁, …, v_{ϱ+1}` of `v` to the frame
`frameCols`, `x⁻¹ s x - 1` lowers the flag of the `v_j` (`LowersFlag`: it maps the span of the first
`j` into that of the first `j - 1`). The sum of the coefficients of `v_j` in the image of `v_{j+1}`
is `simpleRootSum` of the `G₁` component of `s`. -/
lemma lowersFlag_besselPairHom (s : 𝔰.besselGraph)
    (h_frame : (x.val * p.matrix).val * v = 𝔰.frameCols) :
    LowersFlag 𝔰.ϱ v (subOnePair (besselPairHom x) s).fst (simpleRootSum s.val.fst) := by
  obtain ⟨N, hN, h_eq, h_sum⟩ := exists_sub_one_mul_frameCols_eq s
  refine ⟨N, hN, ?_, h_sum⟩
  rw [subOnePair_besselPairHom_fst, Matrix.mul_assoc, h_frame, Matrix.mul_assoc, h_eq,
    initCols_eq_of_frame h_frame, Matrix.mul_assoc]

/-- Take a point `x` such that `x p` takes `i₀` to `definiteCols` and takes the columns of `v` to
`frameCols`. Then every `s` in `besselGraph` (the group `R`) satisfies `InducesOn` for the two
components of `subOnePair (besselPairHom x) s`. That is, `x⁻¹ s x` acts by the image of `s` in `H`
on the image of `i₀`, modulo the span of `v₁, …, v_ϱ`. -/
lemma inducesOn_besselPairHom (s : 𝔰.besselGraph)
    (h_isometry : (x.val * p.matrix).val * i₀ = 𝔰.definiteCols)
    (h_frame : (x.val * p.matrix).val * v = 𝔰.frameCols) :
    InducesOn 𝔰.ϱ v i₀ (subOnePair (besselPairHom x) s).fst
      (subOnePair (besselPairHom (ε := ε) x) s).snd := by
  have h_inv : (x.val * p.matrix)⁻¹.val * 𝔰.definiteCols = i₀ := by
    rw [← h_isometry, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  obtain ⟨C, hC⟩ := exists_sub_one_mul_definiteCols_eq s
  refine ⟨C, ?_⟩
  rw [subOnePair_besselPairHom_fst, subOnePair_besselPairHom_snd, Matrix.mul_assoc, h_isometry,
    Matrix.mul_assoc, hC, initCols_eq_of_frame h_frame, Matrix.mul_add, ← Matrix.mul_assoc, h_inv,
    Matrix.mul_assoc]

/-- Let `x` be in `G₁` and `p.matrix` the unitary matrix of `UnitarySignFrame`, with
`p.matrixᴴ J₁ p.matrix = diag(ε)`. Suppose `x * p.matrix` takes the columns of `v` to `frameCols`,
the frame `e₁, …, e_ϱ, z`. Let `g` be in `positionGroup ε v`: the `g` in `USign ε` such that `g - 1`
maps the span of the first `j` columns of `v` into the span of the first `j - 1`, for the `j` up to
a fixed bound. Then `g` is the first component `x⁻¹ s x` of `besselPairHom x s` for some `s` in
`besselGraph` (the group `R`). -/
lemma exists_besselPairHom_fst_eq (h_frame : (x.val * p.matrix).val * v = 𝔰.frameCols)
    {g : USign ε} (hg : g ∈ positionGroup ε v) :
    ∃ s : 𝔰.besselGraph, (besselPairHom x s).fst = g := by
  -- Write `g` as `x⁻¹ g₁ x` in the frame of signs; then `g₁` lowers the flag of the frame.
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : 𝔰.G₁, frameEquiv (x⁻¹ * g₁ * x) = g :=
    ⟨x * frameEquiv.symm g * x⁻¹, by simp [mul_assoc]⟩
  have h_conj : (g₁ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1 =
      (x.val * p.matrix).val * ((g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) *
        (x.val * p.matrix)⁻¹.val := by
    simp [← hg₁, frameEquiv, U.conj, mul_sub, sub_mul, mul_assoc]
  obtain ⟨σ, N, hN_tri, hN, -⟩ := hg
  have h_lowers : ((g₁ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) * 𝔰.frameCols =
      𝔰.isotropicCols * N := by
    rw [h_conj, ← h_frame, ← Matrix.mul_assoc, Units.inv_mul_cancel_right, Matrix.mul_assoc, hN,
      initCols_eq_of_frame h_frame, Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]
  obtain ⟨s, hs⟩ : ∃ s : 𝔰.besselGraph, s.val.fst = g₁ := exists_besselGraph_fst_eq hN_tri h_lowers
  exact ⟨s, by simp [besselPairHom, hs, ← hg₁]⟩

end Point

/-- The bound `8 n √r M` of `IsPosition.exists_mul_eq_frameCols_and_besselLength_le` at
`M = (3 B + a) ^ (2 n)` is at most `b ^ (5 n)` when `1 ≤ B`, `3 B + a ≤ b ^ 2` and `8 n r ≤ b`. -/
lemma mul_sqrt_mul_pow_le_pow {B b : ℝ} {a : ℕ} (hB : 1 ≤ B) (hb : 3 * B + a ≤ b ^ 2)
    (hb_rank : 8 * 𝔰.n * 𝔰.r ≤ b) :
    8 * 𝔰.n * (√𝔰.r * (3 * B + a) ^ (2 * 𝔰.ϱ + 2)) ≤ b ^ (5 * 𝔰.n) := by
  have hr : (1 : ℝ) ≤ 𝔰.r := Nat.one_le_cast.2 Fintype.card_pos
  have hb_one : 1 ≤ b := by nlinarith [Nat.one_le_cast (α := ℝ).2 (Nat.le_add_left 1 𝔰.ϱ)]
  calc _ ≤ 8 * 𝔰.n * (𝔰.r * (b ^ 2) ^ (2 * 𝔰.ϱ + 2)) := by
        gcongr
        exact Real.sqrt_le_iff.2 ⟨by positivity, le_self_pow₀ hr two_ne_zero⟩
    _ = 8 * 𝔰.n * 𝔰.r * b ^ (4 * (𝔰.ϱ + 1)) := by ring
    _ ≤ b * b ^ (4 * (𝔰.ϱ + 1)) := by gcongr
    _ ≤ b ^ (5 * 𝔰.n) := (pow_succ' b _).ge.trans (pow_le_pow_right₀ hb_one (by lia))

/-- Split the coordinates of `G₁` into `X` and `2 n` more (by `e`), and those of `H` into `X` and
one more (by `τ`). Let the parameter `l` of `U(ε)` be steep with bound `B ≥ 1` (its lowest `K`-type
has weight `0` on `X` and decreasing weight in `[-3 B, -B]` on the others, where the signs
alternate), and let the lowest `K`-type of the parameter `u` of `H` have weight `a` at the last
coordinate and `0` on `X`. Let both parameters have entries of modulus at most `L` and large gap
(`HasLargeGap`: for `2λ` with `N` coordinates, entries of `λ` at coordinates of opposite sign differ
by at least `500 N³ + excess`), where `10 ^ 30 ((r + k)² log β)³ ≤ excess`. If `10 ^ 12 ≤ β`,
`r + k + L ≤ β`, `3 B + a ≤ b ^ 2` and `8 n r ≤ b`, there is a point `x` whose length
`besselLength x`, the infimum of `‖s x‖ + 1` over `s` in `R`, is at most `b ^ (5 n)`, and such that
the volume of `{‖x⁻¹ s x - 1‖ ≤ 1}` in `R` is at most `β ^ (20 (r + k)²)` times the modulus of the
period. The period is the integral over `s` in `R`, with image `t` in `H`, of `c_l(x⁻¹ s x)` times
the conjugate of `c_u(t)` times `exp (conj σ - σ)`. Here `c_l = l.dsCoeff` and `c_u = u.dsCoeff` are
the discrete series coefficients, and `σ = simpleRootSum s` is the sum of the entries of `s` just
above the diagonal on the frame `e₁, …, e_ϱ, z`. -/
theorem IsSteep.exists_stationary_point {X : Type} [Fintype X] {l : HCParam ε}
    {u : HCParam (1 : 𝔰.κ → ℤˣ)} {e : X ⊕ Fin (2 * 𝔰.ϱ + 2) ≃ 𝔰.BesselIndex} {B b β : ℝ}
    {a L excess : ℕ} (h_steep : IsSteep l B e) (τ : X ⊕ Unit ≃ 𝔰.κ)
    (ha : ∀ i : 𝔰.κ, u.lowestKType i = if i = τ (Sum.inr ()) then (a : ℤ) else 0)
    (hB : 1 ≤ B) (hb : 3 * B + a ≤ b ^ 2) (hb_rank : 8 * 𝔰.n * 𝔰.r ≤ b)
    (hl : l.HasLargeGap excess) (hu : u.HasLargeGap excess)
    (hL : ∀ i : 𝔰.BesselIndex, |l i| ≤ L) (hK : ∀ i : 𝔰.κ, |u i| ≤ L)
    (hβ : 10 ^ 12 ≤ β) (h_rank : 𝔰.r + 𝔰.k + L ≤ β)
    (h_excess : 10 ^ 30 * ((𝔰.r + 𝔰.k) ^ 2 * β.log) ^ 3 ≤ excess) :
    ∃ x : 𝔰.G₁,
      besselLength x ≤ b ^ (5 * 𝔰.n) ∧
      𝔰.besselGraphMeasure.real
          {s : 𝔰.besselGraph | ‖(subOnePair (besselPairHom (ε := ε) x) s).fst‖ ≤ 1} ≤
        β ^ (20 * (𝔰.r + 𝔰.k) ^ 2) *
          ‖∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
            (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
            ∂𝔰.besselGraphMeasure‖ := by
  classical
  have : 𝔰.besselGraphMeasure.IsMulRightInvariant := 𝔰.besselGraphMeasure_isMulRightInvariant
  have : IsFiniteMeasureOnCompacts 𝔰.besselGraphMeasure :=
    𝔰.besselGraphMeasure_finiteOnCompacts
  have : Nonempty 𝔰.κ := ⟨τ (Sum.inr ())⟩
  -- The stationary position with `n` vectors, where the weight of `u` lies in `[0, a]`; there are
  -- `2 n` coordinates of `G₁` and one coordinate of `H` outside `X`.
  let e' : X ⊕ Fin 1 ≃ 𝔰.κ := ((Equiv.refl X).sumCongr finOneEquiv).trans τ
  have hX_sign (y : X) : (1 : 𝔰.κ → ℤˣ) (e' (Sum.inl y)) = 1 := Pi.one_apply _
  have hX_zero (y : X) : u.lowestKType (e' (Sum.inl y)) = 0 := by simp [e', ha]
  obtain ⟨v, i₀, hP, h_norm, -, -, h_pow_le⟩ :=
    h_steep.exists_isStationary (k := u) (e' := e') (d := 𝔰.ϱ) (B' := a) hB (by omega) hX_sign
      hX_zero (by simp) (Subsingleton.strictMono _) a.cast_nonneg (by simp [e', ha])
  -- The point: with `μ` the weight of the lowest `K`-type of `l` as a diagonal matrix, the vectors
  -- `μ ^ c v₁` continue `v₁, …, v_n`.
  have h_one_le : 1 ≤ 3 * B + a := by linarith [a.cast_nonneg (α := ℝ)]
  rw [pow_one] at h_norm
  obtain ⟨x, h_isometry, h_frame, h_len⟩ : ∃ x : 𝔰.G₁,
      (x.val * p.matrix).val * i₀ = 𝔰.definiteCols ∧ (x.val * p.matrix).val * v = 𝔰.frameCols ∧
        besselLength x ≤ 8 * 𝔰.n * (√𝔰.r * (3 * B + a) ^ (2 * 𝔰.ϱ + 2)) :=
    hP.exists_mul_eq_frameCols_and_besselLength_le h_norm (one_le_pow₀ h_one_le)
      hP.pow_mulVec_col_zero h_pow_le fun c c' hc ↦ by rw [hP.gram_pow_mulVec hc, h_norm]
  refine ⟨x, h_len.trans (mul_sqrt_mul_pow_le_pow hB hb hb_rank), ?_⟩
  -- The group of the position is `x⁻¹ R x`. The period over it bounds the volume of the set where
  -- both components have norm at most `β + 1`.
  let Large : Set 𝔰.besselGraph := {s : 𝔰.besselGraph |
    ‖((besselPairHom (ε := ε) x s).fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ β + 1 ∧
      ‖((besselPairHom (ε := ε) x s).snd : Matrix 𝔰.κ 𝔰.κ ℂ)‖ ≤ β + 1}
  have h_period : 𝔰.besselGraphMeasure Large ≤ ENNReal.ofReal (β ^ (20 * (𝔰.r + 𝔰.k) ^ 2) *
      ‖∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
        (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
        ∂𝔰.besselGraphMeasure‖) :=
    hP.period_lower_bound_of_surjective h_steep hB hX_sign hX_zero (by simp [ha, ite_nonneg])
      (by simp) hl hu hL hK hβ h_rank h_excess 𝔰.besselGraphMeasure
      (isProperMap_besselPairHom_fst x) (fun _ ↦ exists_besselPairHom_fst_eq h_frame)
      (lowersFlag_besselPairHom · h_frame) (inducesOn_besselPairHom · h_isometry h_frame)
  -- This set contains the unit ball, as `H` is compact.
  have h_ball : {s : 𝔰.besselGraph | ‖(subOnePair (besselPairHom (ε := ε) x) s).fst‖ ≤ 1} ⊆
      Large := by
    have hβ_one : 1 ≤ β := le_trans (by norm_num) hβ
    refine fun s hs ↦ ⟨(norm_le_insert' _ 1).trans (add_le_add (norm_one.trans_le hβ_one) hs), ?_⟩
    rw [besselPairHom_snd_val, CStarRing.norm_of_mem_unitary (U_one_mem_unitaryGroup s.val.snd)]
    linarith
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono h_ball).trans h_period)

end DiscreteSeries

end New

/-! ## The Bessel integral -/

namespace New.DiscreteSeries

open Matrix Fintype Complex Norms.L2Operator MeasureTheory ComplexConjugate ENNReal HCParam
  InnerProductSpace ContinuousLinearMap

variable {𝔰 : Shape} {I : Type*} {ε : 𝔰.BesselIndex → ℤˣ} [Fintype I] [DecidableEq I]
  [UnitarySignFrame 𝔰 ε]

/-- The map `(y, s) ↦ s y` carries the measures of 𝖴∖G₁ and of the Bessel group `R = 𝖴 H` to the
Haar measure of G₁. -/
lemma measurePreserving_unfold_besselGraphMeasure :
    MeasurePreserving (fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ q.snd.val.fst * q.fst)
      (besselQuotMeasure.prod 𝔰.besselGraphMeasure) volume := by
  refine ⟨by fun_prop, Measure.ext_of_lintegral _ fun (g : 𝔰.G₁ → ℝ≥0∞) (hg : Measurable g) ↦ ?_⟩
  simp (disch := fun_prop) only [lintegral_map, lintegral_prod,
    lintegral_unfold_besselGraphMeasure (x := 1) g hg, one_mul]

variable (l : HCParam ε) (rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ) (x : 𝔰.G₁)
  (v : EuclideanSpace ℂ I)

/-- The volume of the set of `s` in `R` with `‖x⁻¹ s x - 1‖ ≤ 1`, the matrix `x⁻¹ s x` being written
in the frame of signs `ε` (the first component of `besselPairHom x s`). -/
noncomputable def besselBallVolume : ℝ≥0∞ :=
  𝔰.besselGraphMeasure {s : 𝔰.besselGraph |
    ‖((besselPairHom (ε := ε) x s).fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1‖ ≤ 1}

/-- The ball whose volume is `besselBallVolume x` has finite measure, as the conjugation by `x` is
proper on `R`. -/
lemma besselBallVolume_ne_top : besselBallVolume (ε := ε) x ≠ ∞ :=
  measure_ball_ne_top_of_isProperMap 𝔰.besselGraphMeasure
    (j := (MonoidHom.fst _ _).comp (besselPairHom x)) (isProperMap_besselPairHom_fst x) 1

/-- The ball whose volume is `besselBallVolume x` has nonzero measure, as it is a neighbourhood of
`1` in `R`. -/
lemma besselBallVolume_ne_zero : besselBallVolume (ε := ε) x ≠ 0 := by
  have h_cont : Continuous fun s : 𝔰.besselGraph ↦ (besselPairHom (ε := ε) x s).fst :=
    (isProperMap_besselPairHom_fst x).continuous
  exact measure_sublevel_ne_zero _

/-- The covering bound: let `N = 9 r ^ 2`. The integral of `(2 / ‖x⁻¹ s y‖) ^ N` over `s` in
`besselGraph` (the group `R`) is at most `16 ^ N` times `besselBallVolume x`, uniformly in `y`. The
norm is the operator norm in the frame of signs `ε` (via `frameEquiv`). -/
lemma lintegral_decay_le_besselBallVolume (y : 𝔰.G₁) :
    ∫⁻ s : 𝔰.besselGraph,
        .ofReal ((2 / ‖(frameEquiv (ε := ε) (x⁻¹ * (s.val.fst * y)) :
          Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖) ^ (9 * 𝔰.r ^ 2))
        ∂𝔰.besselGraphMeasure ≤
      .ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x := by
  let j : 𝔰.besselGraph →* USign ε := (MonoidHom.fst _ _).comp (besselPairHom x)
  have hj_apply (s : 𝔰.besselGraph) : j s = frameEquiv (x⁻¹ * s.val.fst * x) := rfl
  -- The general covering bound for the proper map `j`, at the point `x⁻¹ y`.
  have hr : 0 < 𝔰.r ^ 2 := pow_pos Fintype.card_pos 2
  refine (lintegral_decay_le 𝔰.besselGraphMeasure (j := j) (isProperMap_besselPairHom_fst x)
    (by lia) (frameEquiv (x⁻¹ * y))).trans_eq' ?_
  simp_rw [hj_apply, ← map_mul, mul_assoc, mul_inv_cancel_left]

variable {l rep v} {excess : ℕ}

/-- If `l` has the gap `500 r ^ 3 + excess` (`HasLargeGap`), its coefficient `c_λ`, which is
`l.dsCoeffInFrame`, satisfies `|c_λ(g)| ≤ (2 / ‖g‖) ^ (j + 9 r ^ 2)` for `j ≤ excess`, the norm
being read in the frame of signs `ε`. -/
lemma norm_dsCoeffInFrame_le (h_gap : l.HasLargeGap excess) {j : ℕ} (hj : j ≤ excess) (g : 𝔰.G₁) :
    ‖l.dsCoeffInFrame g‖ ≤
      (2 / ‖(frameEquiv (ε := ε) g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖) ^
        (j + 9 * 𝔰.r ^ 2) := by
  have h_sq : 𝔰.r ^ 2 ≤ 𝔰.r ^ 3 := pow_le_pow_right₀ Fintype.card_pos (by lia)
  have h_exponent : j + 9 * 𝔰.r ^ 2 ≤ gapThreshold 𝔰.BesselIndex excess := by grind
  exact norm_dsCoeff_le_pow h_gap (mod_cast h_exponent) _

/-- For a continuous representation `rep`, the integrand `besselIntegrand l rep x v y s`, which is
`c_λ(x⁻¹ s y) π(s)⁻¹ v` with `c_λ = l.dsCoeffInFrame`, is jointly continuous in `y` and `s`. -/
lemma continuous_besselIntegrand (h_cont : Continuous rep) :
    Continuous (besselIntegrand l rep x v).uncurry := by
  change Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦
    l.dsCoeffInFrame (x⁻¹ * (q.snd.val.fst * q.fst)) •
      wave (-simpleRootSum q.snd.val.fst) • WithLp.toLp 2 ((rep q.snd.val.snd⁻¹).val *ᵥ v.ofLp)
  fun_prop [simpleRootSum, wave]

/-- For a unit vector `v`, the norm of the integrand `c_λ(x⁻¹ s y) π(s)⁻¹ v` is `|c_λ(x⁻¹ s y)|`,
as `π` is unitary. -/
lemma enorm_besselIntegrand (hv_norm : ‖v‖ = 1) (y : 𝔰.G₁) (s : 𝔰.besselGraph) :
    ‖besselIntegrand l rep x v y s‖ₑ = ‖l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y))‖ₑ := by
  simp [besselIntegrand, ← ofReal_norm, norm_smul, hv_norm, Unitary.norm_map]

/-- For a unit vector `v` and a parameter `l` of gap `500 r³ + excess`, the integral over `R` of the
norm of `besselIntegrand l rep x v y` is at most `16 ^ (9 r ^ 2)` times `besselBallVolume x`, the
volume of `{‖x⁻¹ s x - 1‖ ≤ 1}` in `R`. -/
lemma lintegral_enorm_besselIntegrand_le (hv_norm : ‖v‖ = 1) (h_gap : l.HasLargeGap excess)
    (y : 𝔰.G₁) :
    ∫⁻ s : 𝔰.besselGraph, ‖besselIntegrand l rep x v y s‖ₑ ∂𝔰.besselGraphMeasure ≤
      .ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x := by
  refine (lintegral_mono fun s ↦ ?_).trans (lintegral_decay_le_besselBallVolume x y)
  grw [enorm_besselIntegrand x hv_norm, ← ofReal_norm,
    norm_dsCoeffInFrame_le h_gap (Nat.zero_le excess), zero_add]

/-- For a continuous representation `rep`, a unit vector `v` and a parameter `l` of gap
`500 r³ + excess`, the integral over `R` defining `besselAverage l rep x v y` converges
absolutely. -/
lemma integrable_besselIntegrand (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) (y : 𝔰.G₁) :
    Integrable (besselIntegrand l rep x v y) 𝔰.besselGraphMeasure :=
  ⟨((continuous_besselIntegrand x h_cont).uncurry_left y).aestronglyMeasurable,
    (lintegral_enorm_besselIntegrand_le x hv_norm h_gap y).trans_lt
      (mul_lt_top ofReal_lt_top (besselBallVolume_ne_top x).lt_top)⟩

/-- Let `rep` be a continuous unitary representation of `H` on `ℂ^I`, `v` a unit vector of `ℂ^I`,
`x` a point of `G₁`, and `l = 2λ` a parameter with coefficient `c_λ = l.dsCoeffInFrame` and large
gap. For `s = (g, h)` in `R` let `π(s)` be the scalar `wave (simpleRootSum g)` times the operator
`besselValueRep rep h` of `rep h`. Let `W = besselAverage l rep x v`, that is,
`W(y) = ∫_R c_λ(x⁻¹ t y) π(t)⁻¹ v dt` for the measure `du dh` on `R = 𝖴 H`. Then
`W(s y) = π(s) W(y)` for all `s` in `R` and `y` in `G₁`. -/
lemma besselAverage_mul (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) (s : 𝔰.besselGraph) (y : 𝔰.G₁) :
    besselAverage l rep x v (s.val.fst * y) =
      wave (simpleRootSum s.val.fst) •
        (besselValueRep rep s.val.snd).val (besselAverage l rep x v y) := by
  -- Substitute `t * s⁻¹` for `t`; the measure is right invariant and `simpleRootSum` is additive.
  have h_wave (t : 𝔰.besselGraph) : wave (-simpleRootSum (t.val.fst * s.val.fst⁻¹)) =
      wave (simpleRootSum s.val.fst) * wave (-simpleRootSum t.val.fst) := by
    simp [simpleRootSum_mul, Filling.simpleRootSum_inv, wave, ← exp_add, add_sub_add_comm]
  have h_point (t : 𝔰.besselGraph) : besselIntegrand l rep x v (s.val.fst * y) (t * s⁻¹) =
      wave (simpleRootSum s.val.fst) •
        (besselValueRep rep s.val.snd).val (besselIntegrand l rep x v y t) := by
    simp [besselIntegrand, h_wave, mul_assoc, smul_smul, mul_left_comm]
  rw [besselAverage, besselAverage, ← integral_mul_right_eq_self _ s⁻¹, funext h_point,
    integral_smul, integral_comp_comm _ (integrable_besselIntegrand x h_cont hv_norm h_gap y)]

/-- Let `rep` be a continuous unitary representation of `H`, `v` a unit vector, and `l = 2λ` a
parameter with coefficient `c_λ = l.dsCoeffInFrame` and large gap. Let `π` be the representation of
`R = 𝖴 H` that is `rep` on `H` and the character `ψ(u) = exp (σ - conj σ)`, `σ = simpleRootSum u`,
on the unipotent group `𝖴`. Then `W = besselAverage l rep x v`, given by
`W(y) = ∫_R c_λ(x⁻¹ s y) π(s)⁻¹ v ds`, is a Bessel function: it is bounded and measurable, with
`W(u y) = ψ(u) W(y)` for `u` in `𝖴` and `W(h y) = rep h W(y)` for `h` in `H`. -/
lemma isBesselFunction_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) : IsBesselFunction rep (besselAverage l rep x v) where
  stronglyMeasurable :=
    (continuous_besselIntegrand x h_cont).stronglyMeasurable.integral_prod_right
  bounded :=
    have h_le (y : 𝔰.G₁) : ‖besselAverage l rep x v y‖ₑ ≤
        .ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x :=
      (enorm_integral_le_lintegral_enorm _).trans
        (lintegral_enorm_besselIntegrand_le x hv_norm h_gap y)
    ⟨_, fun y ↦ toReal_mono (mul_ne_top ofReal_ne_top (besselBallVolume_ne_top x)) (h_le y)⟩
  map_unipotent_mul s hs y := by
    simpa using besselAverage_mul x h_cont hv_norm h_gap (𝔰.besselGraphChart ⟨⟨s, hs⟩, 1⟩) y
  map_unitary_mul k y := by
    simpa [simpleRootSum_eq_zero_of_mem_besselH, wave, besselValueRep] using
      besselAverage_mul x h_cont hv_norm h_gap (𝔰.besselGraphChart ⟨1, k⟩) y

/-- Let `rep` be a continuous unitary representation of `H` on `ℂ^I`, `v` a unit vector of `ℂ^I`,
`x` a point of `G₁`, and `l = 2λ` a parameter with coefficient `c_λ = l.dsCoeffInFrame`, formal
degree `deg` and large gap. Let `W = besselAverage l rep x v`. Then convolution with the idempotent
kernel `e_λ = deg c_λ` reproduces `W`: `∫ e_λ(a⁻¹) W(y a) da = W(y)` for all `y` in `G₁`. -/
lemma convolve_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) :
    convolve (besselAverage l rep x v) (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) =
      besselAverage l rep x v := by
  -- Exchange the two integrals and use the product formula of the kernel `deg * c_λ`.
  have h_kernel : IsIdempotentKernel fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g :=
    isIdempotentKernel_dsCoeffInFrame h_gap
  have h_reprod (g : 𝔰.G₁) :
      ∫ a : 𝔰.G₁, l.formalDegree * l.dsCoeffInFrame a⁻¹ * l.dsCoeffInFrame (g * a) =
        l.dsCoeffInFrame g := by
    have h_deg : (l.formalDegree : ℂ) ≠ 0 := ofReal_ne_zero.2 (formalDegree_pos h_gap).ne'
    have h_one : l.dsCoeffInFrame (1 : 𝔰.G₁) = 1 := by simp [dsCoeffInFrame]
    have h_product := h_kernel.integral_inv_mul_translate g 1
    simp only [mul_one, h_one, div_mul_cancel₀ _ h_deg] at h_product
    rw [← mul_right_inj' h_deg, ← h_product, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun a ↦ mul_left_comm ..)
  funext y
  have h_reprod_integrand (s : 𝔰.besselGraph) :
      ∫ a : 𝔰.G₁, (l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s =
        besselIntegrand l rep x v y s := by
    simp [besselIntegrand, smul_smul _ (l.dsCoeffInFrame (_ : 𝔰.G₁)), ← mul_assoc,
      integral_smul_const, h_reprod]
  -- The double integral converges, by the covering bound and the integrability of the kernel.
  have h_int : Integrable (Function.uncurry fun (a : 𝔰.G₁) (s : 𝔰.besselGraph) ↦
      (l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s)
      (volume.prod 𝔰.besselGraphMeasure) := by
    have h_integrand_cont : Continuous (besselIntegrand l rep x v).uncurry :=
      continuous_besselIntegrand x h_cont
    refine ⟨Continuous.aestronglyMeasurable (by fun_prop), (lintegral_prod_le _).trans_lt ?_⟩
    calc ∫⁻ a : 𝔰.G₁, ∫⁻ s : 𝔰.besselGraph,
          ‖(l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s‖ₑ
          ∂𝔰.besselGraphMeasure
      _ ≤ ∫⁻ a : 𝔰.G₁, ‖l.formalDegree * l.dsCoeffInFrame a⁻¹‖ₑ *
          (.ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x) := by
        simp_rw [enorm_smul, lintegral_const_mul' _ _ enorm_ne_top]
        grw [lintegral_enorm_besselIntegrand_le x hv_norm h_gap]
      _ < ∞ := by
        rw [lintegral_mul_const'' _ (by fun_prop)]
        exact mul_lt_top h_kernel.integrable.comp_inv.hasFiniteIntegral
          (mul_lt_top ofReal_lt_top (besselBallVolume_ne_top x).lt_top)
  simp only [besselAverage, convolve, ← integral_smul, integral_integral_swap h_int,
    h_reprod_integrand]

/-- For a unit vector `v`, the norm of `besselAverage l rep x v y` is at most the integral of
`|c_λ(x⁻¹ s y)|` over `s` in `R`, where `c_λ = l.dsCoeffInFrame`. -/
lemma enorm_besselAverage_le (hv_norm : ‖v‖ = 1) (y : 𝔰.G₁) :
    ‖besselAverage l rep x v y‖ₑ ≤
      ∫⁻ s : 𝔰.besselGraph, ‖l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y))‖ₑ
        ∂𝔰.besselGraphMeasure := by
  simp_rw [← enorm_besselIntegrand (rep := rep) x hv_norm]
  exact enorm_integral_le_lintegral_enorm _

/-- Let `rep` be a continuous unitary representation of `H`, `v` a unit vector, and `l = 2λ` a
parameter with coefficient `c_λ = l.dsCoeffInFrame` and large gap. Then
`W = besselAverage l rep x v`, given by `W(y) = ∫_R c_λ(x⁻¹ s y) π(s)⁻¹ v ds` with `π` the unitary
representation of `R = 𝖴 H` in `besselIntegrand`, is integrable for `besselQuotMeasure`, the measure
on G₁ that computes integrals over 𝖴∖G₁. -/
lemma integrable_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) : Integrable (besselAverage l rep x v) besselQuotMeasure := by
  -- The upper bound of `‖W‖` unfolds to the integral of `|c_λ|` over G₁.
  have h_coeff_int : Integrable (l.dsCoeffInFrame : 𝔰.G₁ → ℂ) :=
    (integrable_const_mul_iff (ofReal_ne_zero.2 (formalDegree_pos h_gap).ne').isUnit _).1
      (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
  refine ⟨(isBesselFunction_besselAverage x h_cont hv_norm
    h_gap).stronglyMeasurable.aestronglyMeasurable, ?_⟩
  calc _ ≤ ∫⁻ y : 𝔰.G₁, ∫⁻ s : 𝔰.besselGraph, ‖l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y))‖ₑ
          ∂𝔰.besselGraphMeasure ∂besselQuotMeasure :=
      lintegral_mono (enorm_besselAverage_le x hv_norm)
    _ = ∫⁻ g : 𝔰.G₁, ‖l.dsCoeffInFrame g‖ₑ :=
      (lintegral_unfold_besselGraphMeasure (‖l.dsCoeffInFrame ·‖ₑ) (by fun_prop)).symm
    _ < ∞ := h_coeff_int.hasFiniteIntegral

/-- The norm is a period. Let `rep` be a continuous unitary representation of `H`, `v` a unit
vector, and `l = 2λ` a parameter with coefficient `c_λ = l.dsCoeffInFrame`, formal degree `deg` and
large gap. Let `W = besselAverage l rep x v`. Then `deg ‖W‖₂ ^ 2 = ⟪v, W(x)⟫`, the norm being that
of L²(𝖴∖G₁), computed by `besselQuotMeasure`. -/
lemma formalDegree_mul_integral_norm_sq_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) :
    ((l.formalDegree * ∫ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ ^ 2 ∂besselQuotMeasure : ℝ) : ℂ) =
      ⟪v, besselAverage l rep x v x⟫_ℂ := by
  -- Insert the integral for one factor of `⟪W y, W y⟫`, unfold, and use that `e_λ` reproduces `W`
  -- at the point `x`.
  set W : 𝔰.G₁ → EuclideanSpace ℂ I := besselAverage l rep x v
  have hW : IsBesselFunction rep W := isBesselFunction_besselAverage x h_cont hv_norm h_gap
  have h_kernel : IsIdempotentKernel fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g :=
    isIdempotentKernel_dsCoeffInFrame h_gap
  -- `Φ` is the integrand of `deg * ⟪W, W⟫` after one factor has been unfolded to G₁.
  let Φ (g : 𝔰.G₁) : ℂ := conj (l.formalDegree * l.dsCoeffInFrame (x⁻¹ * g)) * ⟪v, W g⟫_ℂ
  have hΦ_int : Integrable Φ := by
    obtain ⟨C, hC⟩ := hW.bounded
    refine (conjCLE.integrable_comp_iff.2 (h_kernel.integrable.comp_mul_left x⁻¹)).mul_bdd
      (c := ‖v‖ * C) hW.stronglyMeasurable.aestronglyMeasurable.const_inner (.of_forall fun g ↦ ?_)
    grw [norm_inner_le_norm, hC]
  have h_insert (y : 𝔰.G₁) : ∫ s : 𝔰.besselGraph, Φ (s.val.fst * y) ∂𝔰.besselGraphMeasure =
      l.formalDegree * (‖W y‖ ^ 2 : ℂ) := by
    have h_point (s : 𝔰.besselGraph) :
        Φ (s.val.fst * y) = l.formalDegree * conj ⟪W y, besselIntegrand l rep x v y s⟫_ℂ := by
      -- Move `π(s)` to the other side of the inner product, as `π(s)⁻¹ = π(s)*`.
      simp [Φ, W, besselAverage_mul x h_cont hv_norm h_gap, besselIntegrand, wave,
        ← Unitary.star_eq_inv, star, adjoint_inner_left, ← exp_conj, neg_add_eq_sub, mul_assoc]
    simp_rw [h_point, integral_const_mul, integral_conj,
      integral_inner (integrable_besselIntegrand x h_cont hv_norm h_gap y), inner_conj_symm]
    exact congrArg _ (inner_self_eq_norm_sq_to_K (W y))
  calc _ = ∫ y : 𝔰.G₁, ∫ s : 𝔰.besselGraph, Φ (s.val.fst * y)
          ∂𝔰.besselGraphMeasure ∂besselQuotMeasure := by
        simp_rw [h_insert, integral_const_mul, ← Complex.ofReal_pow, integral_complex_ofReal,
          Complex.ofReal_mul]
    _ = ∫ g : 𝔰.G₁, Φ g := by
      have h_unfold := measurePreserving_unfold_besselGraphMeasure (𝔰 := 𝔰)
      rw [← h_unfold.map_eq] at hΦ_int ⊢
      rw [integral_map h_unfold.aemeasurable hΦ_int.aestronglyMeasurable]
      exact (integral_prod _ (hΦ_int.comp_measurable h_unfold.measurable)).symm
    _ = ∫ a : 𝔰.G₁, ⟪v, (l.formalDegree * l.dsCoeffInFrame a⁻¹) • W (x * a)⟫_ℂ := by
      rw [← integral_mul_left_eq_self _ x]
      simp only [Φ, inv_mul_cancel_left, inner_smul_right, ← h_kernel.apply_inv]
    _ = ⟪v, convolve W (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) x⟫_ℂ :=
      integral_inner (hW.integrable_smul h_kernel.integrable.comp_inv x) v
    _ = ⟪v, W x⟫_ℂ := by rw [convolve_besselAverage x h_cont hv_norm h_gap]

/-- Let `rep` be a continuous unitary representation of `H` on `ℂ^I`, `v` a vector of `ℂ^I` such
that `⟪v, rep k v⟫` is the coefficient of the parameter `u` at each `k` in `H`, and `l = 2λ` a
parameter with coefficient `c_λ = l.dsCoeffInFrame` and large gap. Let `π` be the representation of
`R = 𝖴 H` that is `rep` on `H` and the character `g ↦ exp (σ - conj σ)`, `σ = simpleRootSum g`, on
`𝖴`. Let `W = besselAverage l rep x v`. Suppose that `besselBallVolume x`, the volume of
`{‖x⁻¹ s x - 1‖ ≤ 1}` in `R`, is at most `P ≥ 0` times the modulus of the period
`∫_R c_λ(x⁻¹ s x) ⟪v, π(s)⁻¹ v⟫ ds`. Then it is at most `P` times the formal degree of `l` times
`‖W‖₂ ^ 2`, the norm being that of L²(𝖴∖G₁). -/
lemma besselBallVolume_le_of_period (h_cont : Continuous rep) (h_gap : l.HasLargeGap excess)
    {u : HCParam (1 : 𝔰.κ → ℤˣ)} {P : ℝ} (hP : 0 ≤ P)
    (hv : ∀ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ⟪v, (besselValueRep rep k).val v⟫_ℂ = u.dsCoeff k)
    (h_period : 𝔰.besselGraphMeasure.real
        {s : 𝔰.besselGraph | ‖(subOnePair (besselPairHom (ε := ε) x) s).fst‖ ≤ 1} ≤
      P * ‖∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
        (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
        ∂𝔰.besselGraphMeasure‖) :
    besselBallVolume (ε := ε) x ≤ .ofReal P *
      (.ofReal l.formalDegree *
        ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure) := by
  have h_sq : ‖v‖ ^ 2 = 1 := by simpa using congrArg norm (hv 1)
  have hv_norm : ‖v‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).1 h_sq
  have h_deg : 0 ≤ l.formalDegree := (formalDegree_pos h_gap).le
  -- The period is `⟪v, W x⟫`, as `conj c_u(h) = conj ⟪v, π(h) v⟫ = ⟪v, π(h)⁻¹ v⟫`.
  have h_inner : ∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
      (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
      ∂𝔰.besselGraphMeasure = ⟪v, besselAverage l rep x v x⟫_ℂ := by
    rw [besselAverage, ← integral_inner (integrable_besselIntegrand x h_cont hv_norm h_gap x)]
    simp [← hv, besselPairHom, laplaceIntegrand, besselIntegrand, wave, inner_smul_right,
      ← Unitary.star_eq_inv, star, adjoint_inner_right, neg_add_eq_sub, mul_assoc,
      mul_comm (cexp _), dsCoeffInFrame]
  have h_nonneg :
      0 ≤ l.formalDegree * ∫ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ ^ 2 ∂besselQuotMeasure :=
    mul_nonneg h_deg (integral_nonneg fun y ↦ sq_nonneg _)
  rw [h_inner, ← formalDegree_mul_integral_norm_sq_besselAverage x h_cont hv_norm h_gap,
    Complex.norm_of_nonneg h_nonneg] at h_period
  -- The set in `h_period` is the ball of `besselBallVolume`, by the definition of `subOnePair`.
  rwa [lintegral_enorm_sq (integrable_besselAverage x h_cont hv_norm h_gap)
      (isBesselFunction_besselAverage x h_cont hv_norm h_gap).memLp_top,
    ← ENNReal.ofReal_mul h_deg, ← ENNReal.ofReal_mul hP,
    le_ofReal_iff_toReal_le (besselBallVolume_ne_top x) (mul_nonneg hP h_nonneg)]

end New.DiscreteSeries

end
