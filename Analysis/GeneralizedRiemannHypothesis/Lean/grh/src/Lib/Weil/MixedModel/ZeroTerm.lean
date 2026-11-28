import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
import Lib.Weil.MixedModel.NamedData
import Lib.Weil.MixedModel.RealTheta

/-!
# Zero term and mixed model of the Weil representation: slices and θ as a sum of slices

This file works with a splitting (Witt decomposition) `D` of `V = (range l ⊕ range k) ⊥ ι V₀`.
A vector `f` of `𝒮 V` is applied to an adelic vector `x` through its theta function:
`f x = θ (ϱ(x) f)` (`New.Space.theta_rho`). The file defines the zero term ev = `D.zeroTerm` :
𝒮 V → 𝒮 V₀ and the slices f[x] = `D.slice x f` = ev(ϱ(l x) f), and proves that the slices obey
the mixed law. It shows that zero terms can be taken in stages and that the zero term depends only
on `ι` and the span of `k`. It studies families obeying the mixed law at adapted points, bounds
sums of slices over rational points and writes θ_V as the sum of θ_{V₀} over the slices.

## Main definitions and results

* `New.Space.Splitting.zeroTerm`: the zero term `𝒮 V → 𝒮 V₀`, the mean of `f (ι y + k b)` over
  `b ∈ 𝔸^p / E^p`; `New.Space.Splitting.slice x` is `D.zeroTerm ∘L V.ϱ (D.lAdelic *ᵥ x)`.
* `New.Space.Splitting.tsum_enorm_slice_le`, `New.Space.Splitting.hasSum_theta_slice`:
  over the rational points `ξ`, `∑_ξ ‖f[ξ]‖ ≤ M ‖f‖` and `θ_V f = ∑_ξ θ_{V₀} (f[ξ])`.
* `New.Space.Splitting.IsAdapted.slice_omega_vacElem`: for `g` adapted to `t`, the slices of
  ω(g) vac are a nonzero constant times `‖vacuumFn (tᴴ x)‖ ^ 2` times the vacuum of `V₀`. The case
  of any `g` when `V₀` is zero needs the Iwasawa decomposition and is
  `New.Space.Splitting.exists_slice_omega_vacElem_of_isEmpty`, in
  `Lib.SiegelWeil.Formula.LagrangianZeroTerms`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Space.Splitting`: A decomposition V = (lE^p ⊕ kE^p) ⊥ ιV₀ over E: isotropic frames l, k with
  l*Jk = 1, an isometry ι from V₀ orthogonal to both, and rk V = rk V₀ + 2p.
* `New.Space.Splitting.IsMixedLaw`: The law T x (ϱ(la + ιw + kb) f) = β(2x + a, b) ϱ(w) T (x + a) f
  of a mixed Schrödinger model, for maps `T x : 𝒮 V → 𝒮 V₀` with `x` in `𝔸^p`.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ThetaInvariance` for sources.
-/

noncomputable section

namespace New.Space.Splitting

/-!
## The zero term and the slices

The Heisenberg operators `V.ϱ y` and the unitary group (`V.ω g`) act on the Banach space `𝒮 V`.
`D.lAdelic`, `D.iAdelic`, `D.kAdelic` are the frames l, ι, k in adelic coordinates. `D.lCoord`,
`D.iCoord`, `D.kCoord` send `l a + ι w + k b` to `a`, `w`, `b`.
-/

open Matrix IsDualFamily NumberField Heisenberg.IsVacuum ContinuousLinearMap

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {n₀ p : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} (x) (f : 𝒮 V)

/-- For a splitting, f in 𝒮(V) and an adelic vector y of V₀, the function b ↦ f(ιy + kb) on 𝔸^p
is continuous and periodic under E^p. -/
lemma isContPeriodic_along_k (y : n₀ → 𝔸 E) :
    IsContPeriodic (New.ratVectors E p) fun b : p → 𝔸 E ↦ f (D.iAdelic *ᵥ y + D.kAdelic *ᵥ b) := by
  refine ⟨by fun_prop, fun γ hγ x ↦ ?_⟩
  -- The vector `k γ` is rational, so `f` is quasi-periodic under it; at `z = ι y + k x` the factor
  -- `β (k γ) z` is 1, as `k` is orthogonal to itself and to `ι`.
  have quasi (z : n → 𝔸 E) : (adelicHeisenberg E s).β (D.kAdelic *ᵥ γ) z * f (D.kAdelic *ᵥ γ + z) =
    f z :=
    calc _ = V.ϱ z f (D.kAdelic *ᵥ γ) := (V.rho_apply ..).symm
      _ = f z := V.isThetaFunctional_rawTheta.left _ (D.kAdelic_mulVec_mem_ratVectors hγ) _
  simpa [D.beta_eq_coords, add_left_comm, mulVec_add] using quasi (D.iAdelic *ᵥ y + D.kAdelic *ᵥ x)

/-- The mean of `f (ι y + k b)` over `b ∈ 𝔸^p / E^p`, as a function of `y`, defines a bounded
linear map from `𝒮 V` to `𝒮 V₀`. -/
lemma exists_zeroTerm :
    ∃ L : 𝒮 V →L[ℂ] 𝒮 V₀, ∀ (f : 𝒮 V) (y : n₀ → 𝔸 E), L f y =
      quotMean (New.ratVectors E p) fun b : p → 𝔸 E ↦ f (D.iAdelic *ᵥ y + D.kAdelic *ᵥ b) := by
  -- Take a point g that splits the coordinates of V into those of the hyperbolic space and of V₀.
  -- The mean ℓ along range k, read through ω(g), satisfies ℓ(w ⊠ v) = c(w) θ(v). So L ω(g) has
  -- to be c ⊠ 1, which is bounded on the translated vacua and hence extends to 𝒮(V).
  obtain ⟨g, -, e, hs, hg⟩ := D.exists_isAdapted_and_frame_eq 1
  have h_coord (w : n₀ → 𝔸 E) : D.iAdelic *ᵥ w = g.adeleMatrix *ᵥ (0 ⊕ᵥ w) ∘ e.symm := by
    simpa [submatrix_mulVec_equiv, frameAt, fromCols_mul_fromBlocks] using
      congrArg (mulVec · (0 ⊕ᵥ w)) hg
  let F (q : (p → 𝔸 E) ⧸ New.ratVectors E p) : 𝒮 V →L[ℂ] ℂ :=
    V.rawTheta ∘L V.ϱ (D.iAdelic *ᵥ 0 + D.kAdelic *ᵥ q.out) ∘L V.ω g
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : 𝒮 V →L[ℂ] ℂ, ∀ f,
      ℓ f = quotMean (New.ratVectors E p) fun b ↦ V.ω g f (D.iAdelic *ᵥ 0 + D.kAdelic *ᵥ b) :=
    ⟨_, strongIntegral_apply _ F fun f ↦ (D.isContPeriodic_along_k _ 0).integrable_out⟩
  -- Translating along the coordinates of V₀ moves the base point of the mean.
  have h_shift (y : n₀ → 𝔸 E) (f : 𝒮 V) : ℓ (V.ϱ ((0 ⊕ᵥ y) ∘ e.symm) f) =
      quotMean (New.ratVectors E p) fun b ↦ V.ω g f (D.iAdelic *ᵥ y + D.kAdelic *ᵥ b) := by
    simp [hℓ, ← h_coord, D.beta_eq_coords, add_comm, omega_rho]
  have h_prod (y : n₀ → 𝔸 E) (w : 𝒮 (hyperbolicSpace E p)) (v : 𝒮 V₀) :
      boxProd hs w (V₀.ϱ y v) = V.ϱ ((0 ⊕ᵥ y) ∘ e.symm) (boxProd hs w v) := by
    simp [← boxProd_rho]
  -- For rational γ the vector ιγ is rational, so v ↦ ℓ(w ⊠ v) is invariant.
  have h_inv (w : 𝒮 (hyperbolicSpace E p)) : V₀.IsRatInvariant (ℓ ∘L boxProd hs (V₂ := V₀) w) := by
    rintro _ ⟨γ, rfl⟩ (v : 𝒮 V₀)
    change ℓ (boxProd hs w (V₀.ϱ (V₀.vecAtPoint γ) v)) = ℓ (boxProd hs w v)
    rw [h_prod, h_shift, hℓ]
    congr! 2 with b
    simpa [D.beta_eq_coords, ← iAdelic.eq_1, ← V₀.ratMap_mulVec_vecAtPoint] using
      V.apply_vecAtPoint_add _ (D.i *ᵥ γ) (D.kAdelic *ᵥ b)
  -- An invariant functional is its value at a fixed vector u times θ, so c(w) = ℓ(w ⊠ u).
  obtain ⟨u, hu⟩ := V₀.isThetaFunctional_rawTheta.exists_eq_apply_smul
  let c : 𝒮 (hyperbolicSpace E p) →L[ℂ] ℂ :=
    ℓ ∘L (boxProd hs (V₁ := hyperbolicSpace E p) (V₂ := V₀)).flip u
  have hc (w : 𝒮 (hyperbolicSpace E p)) (v : 𝒮 V₀) : ℓ (boxProd hs w v) = c w * V₀.rawTheta v :=
    DFunLike.congr_fun (hu _ (h_inv w)) v
  -- `K z` is the image under c ⊠ 1 of ϱ(z) vac = ϱ(z₁) vac ⊠ ϱ(z₂) vac.
  let K (z : n → 𝔸 E) : 𝒮 V₀ :=
    c ((hyperbolicSpace E p).ϱ (z ∘ e ∘ .inl) (hyperbolicSpace E p).vacElem) • V₀.ϱ (z ∘ e ∘ .inr)
      V₀.vacElem
  have hK_bdd (z : n → 𝔸 E) : ‖K z‖ ≤ ‖c‖ * ‖(hyperbolicSpace E p).vacElem‖ * ‖V₀.vacElem‖ := by
    grw [norm_smul, c.le_opNorm]
    simp [Heisenberg.Rep.norm_map]
  have h_vac (y : n₀ → 𝔸 E) (z : n → 𝔸 E) :
      V₀.rawTheta (V₀.ϱ y (K z)) = ℓ (V.ϱ ((0 ⊕ᵥ y) ∘ e.symm) (V.ϱ z V.vacElem)) := by
    rw [← boxProd_vacElem hs (V₁ := hyperbolicSpace E p) (V₂ := V₀), rho_boxProd hs z, ← h_prod, hc,
      map_smul, map_smul, smul_eq_mul]
  -- `exists_lift` gives a bounded `T` that acts as if it sent ϱ(z) vac to `K z`: an identity
  -- M (K z) = N (ϱ(z) vac) for all z implies M ∘ T = N.
  obtain ⟨T, hT⟩ := exists_lift (H := adelicHeisenberg E s) (Y := ℂ) (K := K) (by fun_prop) hK_bdd
  refine ⟨T ∘L V.ω g⁻¹, fun f y ↦ ?_⟩
  calc T (V.ω g⁻¹ f) y = ℓ (V.ϱ ((0 ⊕ᵥ y) ∘ e.symm) (V.ω g⁻¹ f)) :=
      hT (V₀.rawTheta ∘L V₀.ϱ y) (ℓ ∘L V.ϱ _) (h_vac y) _
    _ = _ := by simp [h_shift, rep_apply_apply]

/-- The zero term along k: the bounded map 𝒮(V) → 𝒮(V₀) with (ev f)(y) the mean of f(ιy + kb)
over b in 𝔸^p modulo E^p. Here f(x) = θ(ϱ(x)f) is the theta function of f. -/
noncomputable def zeroTerm : 𝒮 V →L[ℂ] 𝒮 V₀ := D.exists_zeroTerm.choose

/-- The zero term of f at y is the mean of f(ιy + kb) over b in 𝔸^p / E^p. -/
lemma zeroTerm_apply (y : n₀ → 𝔸 E) : D.zeroTerm f y =
    quotMean (New.ratVectors E p) fun b : p → 𝔸 E ↦ f (D.iAdelic *ᵥ y + D.kAdelic *ᵥ b) :=
  D.exists_zeroTerm.choose_spec f y

/-- For a Witt decomposition `D` of `V` with isotropic frame `k` and complement `V₀`, the zero term
`D.zeroTerm : 𝒮(V) → 𝒮(V₀)` averages the theta function of `f` over translates by `k 𝔸^p` modulo
`E^p`. It is unchanged when `f` is first moved by `V.ϱ` at `D.kAdelic *ᵥ x`, which is the vector
`k x` in standard coordinates, for every `x : p → 𝔸 E` (a vector of 𝔸^p). -/
lemma zeroTerm_rho_kAdelic : D.zeroTerm (V.ϱ (D.kAdelic *ᵥ x) f) = D.zeroTerm f := by
  ext y
  -- The mean over b is invariant under translation by x.
  rw [zeroTerm_apply, zeroTerm_apply, ← quotMean_translate (D.isContPeriodic_along_k f y) x]
  simp [D.beta_eq_coords, add_assoc, mulVec_add]

lemma zeroTerm_rho_iAdelic : D.zeroTerm (V.ϱ (D.iAdelic *ᵥ x) f) = V₀.ϱ x (D.zeroTerm f) := by
  ext
  simp [zeroTerm_apply, D.beta_eq_coords, add_right_comm, mulVec_add]

/-- The slice at x in 𝔸^p: the bounded map f ↦ f[x] = ev(ϱ(lx)f) from 𝒮(V) to 𝒮(V₀), where ev is the
zero term `New.Space.Splitting.zeroTerm`. -/
noncomputable def slice (x : p → 𝔸 E) : 𝒮 V →L[ℂ] 𝒮 V₀ := D.zeroTerm ∘L V.ϱ (D.lAdelic *ᵥ x)

lemma slice_zero : D.slice 0 = D.zeroTerm := by
  ext
  simp [slice]

/-- For a Witt decomposition `D` of `V` as `(l E^p ⊕ k E^p) ⊥ ι V₀`, the slices
`D.slice x : f ↦ f[x]` (x in 𝔸^p) satisfy the mixed Schrödinger law
`New.Space.Splitting.IsMixedLaw`: (ϱ(la + ιw + kb)f)[x] = ψ(½ȷ b*(2x + a)) ϱ(w) f[x + a], for x, a,
b in 𝔸^p, w an adelic vector of V₀ and f in 𝒮(V). Here the phase is the bicharacter `β (2 x + a) b`
of `adelicHeisenberg E 1`, and ȷ = −ȷ̄ is the element of E from the Weil data. -/
@[simp]
lemma isMixedLaw_slice : D.IsMixedLaw D.slice :=
  isMixedLaw_comp_rho _ D.zeroTerm_rho_kAdelic D.zeroTerm_rho_iAdelic

end New.Space.Splitting

namespace New.Space

/-! ## Zero terms in stages and independence of the splitting -/

open Matrix Splitting

variable {E n n₀ p n₁ q : Type*} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} [Fintype n₀] [DecidableEq n₀] {s₀ : n₀ → ℤˣ}
  (V : Space E n s) (V₀ : Space E n₀ s₀) [Fintype n₁] [DecidableEq n₁] [Fintype q] [DecidableEq q]
  {s₁ : n₁ → ℤˣ} {V₁ : Space E n₁ s₁}

/-- The rational map of a matrix i carries the frame x₀⁻¹k of V₀, for a rational matrix k, to the
frame x⁻¹(ik) of V, where x and x₀ are the points of V and V₀. -/
@[simp]
lemma ratMap_mul_toAdele (i : Matrix n n₀ E) (k : Matrix n₀ p E) :
    V.ratMap V₀ i * (V₀.x⁻¹.val * k.map toAdele) = V.x⁻¹.val * (i * k).map toAdele := by
  simp [ratMap, Matrix.mul_assoc]

/-- The rational maps x⁻¹ i x₀ between spaces, formed with their points, compose like the matrices i
that define them. -/
lemma ratMap_mul_ratMap (i : Matrix n n₀ E) (k : Matrix n₀ n₁ E) :
    V.ratMap V₀ i * V₀.ratMap V₁ k = V.ratMap V₁ (i * k) := by
  simp [ratMap, Matrix.mul_assoc]

variable [Fintype p] [DecidableEq p] {V V₀} (D : V.Splitting V₀ p) (D' : V₀.Splitting V₁ q)

omit [DecidableEq p] [Fintype q] [DecidableEq q] in
lemma map_mulVec_mem_ratVectors (c : Matrix q p E) :
    ∀ b ∈ New.ratVectors E p, c.map toAdele *ᵥ b ∈ New.ratVectors E q := by
  rintro _ ⟨a, rfl⟩
  exact ⟨c *ᵥ a, funext (toAdele.map_mulVec c a)⟩

namespace Splitting

/-- The adelic frame k of a composite splitting consists of the frame k of the first splitting and
the image under its embedding ι of the frame k of the second. -/
lemma comp_kAdelic : (D.comp D').kAdelic = D.kAdelic.fromCols (D.iAdelic * D'.kAdelic) := by
  simp [kAdelic, comp, fromCols_map, iAdelic, ratMap, Matrix.mul_assoc]

/-- Zero terms can be taken in stages. For splittings `D` of V over V₀ and `D'` of V₀ over V₁, the
zero term of the composite splitting `D.comp D'` is the zero term of `D'` applied after that of `D`.
Here the zero term along `k` is the map 𝒮(V) → 𝒮(V₀) sending f to y ↦ the mean of θ(ϱ(ιy + kb) f)
over b ∈ 𝔸^p modulo E^p. -/
lemma zeroTerm_comp [WeilData E]
    (f : 𝒮 V) : (D.comp D').zeroTerm f = D'.zeroTerm (D.zeroTerm f) := by
  -- The mean over `𝔸^(p ⊕ q)` is the mean over the `q` block of the mean over the `p` block.
  ext y
  let φ : (q → 𝔸 E) × (p → 𝔸 E) →+ (p ⊕ q → 𝔸 E) :=
    .mk' (fun a ↦ a.2 ⊕ᵥ a.1) (by simp [funext_iff])
  have hφ : Continuous φ :=
    Homeomorph.sumArrowHomeomorphProdArrow.continuous_invFun.comp continuous_swap
  have h_rat : ∀ a ∈ New.ratVectors E q, ∀ b ∈ New.ratVectors E p,
      φ (a, b) ∈ New.ratVectors E (p ⊕ q) := by simp_all [φ, mem_ratVectors]
  have h_point (a : q → 𝔸 E) (b : p → 𝔸 E) :
      (D.comp D').iAdelic *ᵥ y + (D.comp D').kAdelic *ᵥ φ (a, b) =
        D.iAdelic *ᵥ (D'.iAdelic *ᵥ y + D'.kAdelic *ᵥ a) + D.kAdelic *ᵥ b := by
    simp [φ, iAdelic, ratMap, comp, Matrix.mul_assoc, kAdelic, fromCols_map, mulVec_add,
      add_right_comm, add_assoc]
  rw [zeroTerm_apply, ← quotMean_quotMean (New.ratVectors E q) (isContPeriodic_along_k f _)
    (New.ratVectors E p) φ hφ h_rat fun b ↦ ⟨(b ∘ Sum.inr, b ∘ Sum.inl), Sum.elim_comp_inl_inr b⟩]
  simp only [h_point, zeroTerm_apply]

/-- If the frame k′ of a second splitting D′ of V over V₀ has no l-coordinate in D and both
splittings read off the same V₀-coordinate, then k′ is spanned by k, with its k-coordinates in D as
coefficients. -/
lemma kAdelic_mul_kCoord_mul_kAdelic (D : V.Splitting V₀ p) (D' : V.Splitting V₀ q)
    (h_lCoord : D.lCoord * D'.kAdelic = 0) (h_iCoord : D'.iCoord = D.iCoord) :
    D.kAdelic * (D.kCoord * D'.kAdelic) = D'.kAdelic := by
  -- Apply the identity k kCoord + ι iCoord + l lCoord = 1 to k′; the last two terms vanish.
  simpa [Matrix.add_mul, ← h_iCoord, h_lCoord, Matrix.mul_assoc] using
    congrArg (· * D'.kAdelic) D.sum_frame_mul_coord_eq_one

/-- The zero term depends only on the embedding ι of V₀ and the span of the frame k. Two splittings
of V over V₀, with isotropic frames k and k′ (of possibly different index sets), have the same
zero-term map 𝒮(V) → 𝒮(V₀) if their embeddings of V₀ coincide and k*Jk′ = 0; given the first
condition, the second says that k and k′ span the same subspace. -/
lemma zeroTerm_congr [WeilData E] (D : V.Splitting V₀ p) (D' : V.Splitting V₀ q)
    (hk : D.kᴴ * V.J * D'.k = 0) (hi : D'.i = D.i) : D'.zeroTerm = D.zeroTerm := by
  -- The frames `D.kAdelic` and `D'.kAdelic` differ by a rational matrix that is onto, which
  -- preserves the mean.
  have hiA : D'.iAdelic = D.iAdelic := by simp [hi, iAdelic]
  have hiT : D'.iCoord = D.iCoord := by rw [iCoord, hiA, iCoord]
  -- As `k` and `k'` are orthogonal, each has no `l`-coordinate in the other splitting, so each is
  -- spanned by the other.
  have hk_symm : D'.kᴴ * V.J * D.k = 0 := by
    simpa [conjTranspose_J, Matrix.mul_assoc] using congrArg conjTranspose hk
  have h_span : D.kAdelic * (D.kCoord * D'.kAdelic) = D'.kAdelic :=
    D.kAdelic_mul_kCoord_mul_kAdelic D' ((V.gram_at_point_eq_map D.k D'.k).trans (by simp [hk])) hiT
  have h_span_symm : D'.kAdelic * (D'.kCoord * D.kAdelic) = D.kAdelic :=
    D'.kAdelic_mul_kCoord_mul_kAdelic D
      ((V.gram_at_point_eq_map D'.k D.k).trans (by simp [hk_symm])) hiT.symm
  let φ : (p → 𝔸 E) →+ (q → 𝔸 E) := (D'.kCoord * D.kAdelic).toLin'
  have h_surj : Function.Surjective φ :=
    fun x ↦ ⟨D.kCoord *ᵥ D'.kAdelic *ᵥ x, by simp [φ, h_span]⟩
  -- The change of frame is the rational Gram matrix `D'.lᴴ * V.J * D.k`.
  have h_change : D'.kCoord * D.kAdelic = (D'.lᴴ * V.J * D.k).map toAdele :=
    V.gram_at_point_eq_map D'.l D.k
  have h_rat : ∀ a ∈ New.ratVectors E p, (D'.kCoord * D.kAdelic) *ᵥ a ∈ New.ratVectors E q := by
    simpa only [h_change] using map_mulVec_mem_ratVectors (D'.lᴴ * V.J * D.k)
  -- Pull the mean over `𝔸^q / E^q` back along the change of frame.
  ext f y
  rw [zeroTerm_apply, ← quotMean_comp (New.ratVectors E p) φ (isContPeriodic_along_k f _) h_rat
    h_surj (toLin' _).continuous_on_pi]
  simp [φ, hiA, h_span_symm, zeroTerm_apply]

end Splitting

end New.Space

namespace New.Space.Splitting

/-!
## Vacua and named finite data in the mixed model at adapted points

This section treats any family `T` of maps that obeys the law of a mixed Schrödinger model of a
splitting `V = l Eᵖ ⊕ V₀ ⊕ k Eᵖ` (`New.Space.Splitting.IsMixedLaw`), at a point `g` adapted to `t`
(`New.Space.Splitting.IsAdapted`). The slices `New.Space.Splitting.slice` are such a family.

* `New.Space.Splitting.IsAdapted.omega_projOn_adelic_of_isMixedLaw`: the values of `T` on a
  vector that is a vacuum above a set `S` of finite places and its conjugate.
* `New.Space.Splitting.IsAdapted.exists_omega_vacElem_of_isMixedLaw`: the law determines the values
  of `T` on ω(g) vac up to a constant.
* `New.Space.Splitting.IsAdapted.omega_schrodingerOp_of_isMixedLaw`: the datum named by `Ψ` becomes
  the datum named by the partial Fourier transform `New.Space.Splitting.sliceDatum` of `Ψ`.

`S.conjClosure` is the union of `S` and its conjugate, `idem S • x` the part of `x` above `S`,
`New.integralBox n S` the vectors integral on `S`, `New.finVec x` the adelic vector `(0, α x)`,
and `half` the finite adele `1/2`.
-/

section MixedModelNames

open MeasureTheory Matrix stdLattice Prod Finset IsIntMatrix RingHom Complex Fock

variable {E n n₀ p : Type*} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s₀ : n₀ → ℤˣ}
  {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) (S : Set (FinPlace E)) (g : G E s)
  (t : GL p (𝔸 E)) (Ψ : (n → 𝔸f E) → ℂ) (a : p → 𝔸f E) (w : n₀ → 𝔸f E) (b : p → 𝔸f E)

/-- The finite adelic vector g⁻¹(l t*⁻¹a + ιw + ktb), formed with the finite parts of the
matrices g⁻¹l t*⁻¹, g⁻¹ι and g⁻¹kt. -/
def finFrameVector : n → 𝔸f E := (D.frameAt g t).map Prod.snd *ᵥ (a ⊕ᵥ b ⊕ᵥ w)

/-- The function Ψ_x(y) = ∫ ψ_f(ȷαᾱ x*b_S) Ψ(g⁻¹(l t*⁻¹x + ιy + ktb)) db. The integral runs over
finite adelic b integral off S, b_S is the S-part of b, and Ô^p has mass one. Here ψ_f(ȷαᾱ ·) is
`selfDualAddChar E`, the character from the Weil data for which Ô is self-dual. -/
def sliceDatum (x : p → 𝔸f E) (y : n₀ → 𝔸f E) : ℂ :=
  ∫ b : p → 𝔸f E in integralBox p Sᶜ, selfDualAddChar E (star x ⬝ᵥ idem S • b) *
    Ψ (D.finFrameVector g t x y b) ∂latticeMeasure E p

/-! ### Coordinates in the frame at `g` -/

omit [WeilData E] in
@[local simp]
lemma smul_finFrameVector (c : 𝔸f E) :
    c • D.finFrameVector g t a w b = D.finFrameVector g t (c • a) (c • w) (c • b) := by
  simp [finFrameVector, frameAt, G.adeleMatrix, fromCols_map, mulVec_smul]

omit [WeilData E] in
/-- The adjoint of the frame recovers the three parts, with those along `l` and `k` exchanged. -/
lemma adjoint_mulVec_finFrameVector :
    ((D.frameAt g t).map Prod.snd)ᴴ *ᵥ D.finFrameVector g t a w b = b ⊕ᵥ a ⊕ᵥ w := by
  -- The standard form is the identity at the finite places, so it may be inserted; the adjoint
  -- of the frame times the frame is then the finite part of the Gram matrix `gram_frameAt`.
  have adj_eq : ((D.frameAt g t).map snd)ᴴ = ((D.frameAt g t)ᴴ * stdForm E s).map snd :=
    Matrix.ext (by simp [stdForm])
  have h_gram : ((D.frameAt g t).map snd)ᴴ * (D.frameAt g t).map snd =
      (fromBlocks (fromBlocks 0 1 1 0) 0 0 (stdForm E s₀)).map snd := by
    rw [adj_eq, ← coe_snd, ← Matrix.map_mul, gram_frameAt]
  rw [finFrameVector, mulVec_mulVec, h_gram]
  -- That Gram matrix swaps the first two blocks and fixes the third.
  simp [stdForm, fromBlocks_map, fromBlocks_mulVec]

omit [WeilData E] in
/-- Every finite adelic vector is given by its three parts in the frame. -/
lemma exists_eq_finFrameVector (y : n → 𝔸f E) :
    ∃ (a : p → 𝔸f E) (w : n₀ → 𝔸f E) (b : p → 𝔸f E), y = D.finFrameVector g t a w b := by
  -- By `adjoint_mulVec_finFrameVector` the adjoint `A` of the frame is onto; the ranks agree, so it
  -- is also injective.
  let A : (n → 𝔸f E) →ₗ[𝔸f E] ((p ⊕ p) ⊕ n₀ → 𝔸f E) := mulVecLin ((D.frameAt g t).map snd)ᴴ
  have h_section (v : (p ⊕ p) ⊕ n₀ → 𝔸f E) :
      A (D.finFrameVector g t (v ∘ .inl ∘ .inr) (v ∘ .inr) (v ∘ .inl ∘ .inl)) = v := by
    rw [mulVecLin_apply, adjoint_mulVec_finFrameVector]
    ext ((i | i) | i) <;> rfl
  have h_bij : Function.Bijective A :=
    OrzechProperty.bijective_of_surjective_of_finrank_le A (fun v ↦ ⟨_, h_section v⟩)
      (by simp +arith [D.card_eq])
  -- The vector built from the three blocks of `A y` has the same image as `y`.
  exact ⟨_, _, _, h_bij.injective (h_section (A y)).symm⟩

omit [WeilData E] in
/-- The hermitian product in the frame: the parts along `l` and `k` pair with each other. -/
@[local simp]
lemma star_dot_finFrameVector (a' : p → 𝔸f E) (w' : n₀ → 𝔸f E) (b' : p → 𝔸f E) :
    star (D.finFrameVector g t a w b) ⬝ᵥ D.finFrameVector g t a' w' b' =
      star a ⬝ᵥ b' + star b ⬝ᵥ a' + star w ⬝ᵥ w' := by
  rw [finFrameVector, star_mulVec_dotProduct, adjoint_mulVec_finFrameVector]
  simp [dotProduct]

omit [WeilData E] in
/-- In an adapted frame, a vector is integral on `S` if and only if its three parts are. Here `g` is
adapted to `t` when the frame matrix g⁻¹(l t*⁻¹, kt, ι) has orthonormal columns at the infinite
places and integral finite entries. -/
lemma IsAdapted.finFrameVector_mem_integralBox {D : V.Splitting V₀ p} {g : G E s}
    {t : GL p (𝔸 E)} (a : p → 𝔸f E) (w : n₀ → 𝔸f E) (b : p → 𝔸f E) (hg : D.IsAdapted g t)
    (S : Set (FinPlace E)) :
    D.finFrameVector g t a w b ∈ integralBox n S ↔
      a ∈ integralBox p S ∧ w ∈ integralBox n₀ S ∧ b ∈ integralBox p S := by
  obtain ⟨-, frame_int⟩ : _ ∧ IsIntMatrix (Ô E) ((D.frameAt g t).map snd) := hg
  suffices (∀ i, D.finFrameVector g t (idem S • a) (idem S • w) (idem S • b) i ∈ Ô E) ↔
      ∀ i, (idem S • b ⊕ᵥ idem S • a ⊕ᵥ idem S • w) i ∈ Ô E by
    simpa [mem_stdLattice, integralBox, and_comm, and_left_comm] using this
  refine ⟨fun h_int ↦ ?_, fun h_int ↦ frame_int.mulVec (by simp_all [intVectors])⟩
  -- The adjoint recovers the three parts, so they are integral.
  simpa [↓adjoint_mulVec_finFrameVector, intVectors] using
    frame_int.conjTranspose.mulVec h_int

/-! ### The law at the finite places -/

universe u_1 u_2 u_3 u_4

/-- The law of the mixed model for the translation by a finite vector with parts `a`, `w`, `b`:
`a` shifts the point `x`, `w` translates the value, and `b` gives the factor
`selfDualAddChar E (½ bᴴ (2 x + a))`. -/
lemma IsMixedLaw.apply_omega_rho_finFrameVector
    {E : Type u_1} {n : Type u_3} {n₀ : Type u_2} {p : Type u_4} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} [Fintype n₀] [DecidableEq n₀] [Fintype p]
    [DecidableEq p] {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p}
    {g : G E s} {t : GL p (𝔸 E)} (a : p → 𝔸f E) (w : n₀ → 𝔸f E) (b : p → 𝔸f E)
    {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀} (hT : D.IsMixedLaw T) (x : p → 𝔸f E) (f : 𝒮 V) :
    T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.ϱ (finVec (D.finFrameVector g t a w b)) f)) =
      selfDualAddChar E (half * star b ⬝ᵥ (x + (x + a))) •
        V₀.ϱ (finVec w) (T (t.val⁻¹ᴴ *ᵥ finVec (x + a)) (V.ω g f)) := by
  -- Move the translation past `V.ω g` and apply the law; `lCoord`, `kCoord`, `iCoord` read off
  -- `t⁻¹ᴴ a`, `t b`, `w`.
  set v : n → 𝔸 E := g.adeleMatrix *ᵥ D.frameAt g t *ᵥ finVec (a ⊕ᵥ b ⊕ᵥ w) with hv
  have h_split : finVec (a ⊕ᵥ b ⊕ᵥ w) = finVec a ⊕ᵥ finVec b ⊕ᵥ finVec w := by
    ext1 ((i | i) | i) <;> rfl
  obtain ⟨h_l, h_k, h_i⟩ : D.lCoord *ᵥ v = t.val⁻¹ᴴ *ᵥ finVec a ∧
      D.kCoord *ᵥ v = t.val *ᵥ finVec b ∧ D.iCoord *ᵥ v = finVec w := by
    simp [hv, h_split, frameAt, G.adeleMatrix, mulVec_add, ← Matrix.mul_assoc]
  have h_add : finVec (x + a) = finVec x + finVec a := by simp [finVec, funext_iff, mul_add]
  -- `finVec` scales by `α`, so `stdAddChar` with the factor `j / 2` becomes `selfDualAddChar` with
  -- `half`.
  have h_char (z : p → 𝔸f E) :
      (stdAddChar E (toAdele (WeilData.j / 2 : E) * star (finVec b) ⬝ᵥ finVec z) : ℂ) =
        selfDualAddChar E (half * star b ⬝ᵥ z) := by
    simp [finVec, stdAddChar, selfDualAddChar_apply, half, dotProduct, mul_sum, fst_sum, snd_sum]
    grind
  have h_phase :
      (adelicHeisenberg E 1).β (t.val⁻¹ᴴ *ᵥ finVec x +
        (t.val⁻¹ᴴ *ᵥ finVec x + t.val⁻¹ᴴ *ᵥ finVec a))
          (t.val *ᵥ finVec b) = selfDualAddChar E (half * star b ⬝ᵥ (x + (x + a))) := by
    simp [dotProduct_mulVec, adelicHeisenberg, star_mulVec, ← conjTranspose_mul, mul_add,
      ← mulVec_add, AddChar.map_add_eq_mul, h_char]
  rw [finFrameVector, ← mulVec_finVec, omega_rho, hT, h_l, h_k, h_i, h_phase, h_add, mulVec_add]

/-- Let `P = V.projOn S` be the projection on the vacua above `S ∪ S̄` (the mean of the finite
Heisenberg operators over `Ô^n` above `S ∪ S̄`, with `S̄` the set of conjugate places), let `T` obey
the law of a mixed model, and let `g` be adapted to `t`. Then the value of `ω(g) P f` at the finite
point `x` vanishes unless `x` is integral on `S ∪ S̄`, and then it is `V₀.projOn S` applied to the
value at the part of `x` off `S ∪ S̄`. The value at a finite point `x` means the value of `T` at
`t⁻¹ᴴ (α x)`, with `α` the finite idele of the Weil data. -/
lemma IsAdapted.omega_projOn_of_isMixedLaw
    {E : Type u_1} {n : Type u_3} {n₀ : Type u_2} {p : Type u_4} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} [Fintype n₀] [DecidableEq n₀] [Fintype p]
    [DecidableEq p] {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p}
    {S : Set (FinPlace E)} {g : G E s} {t : GL p (𝔸 E)} {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀}
    (hg : D.IsAdapted g t) (hT : D.IsMixedLaw T) (x : p → 𝔸f E) (f : 𝒮 V) :
    T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.projOn S f)) =
      boxIndicator p S.conjClosure x •
        V₀.projOn S (T (t.val⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • x)) (V.ω g (V.projOn S f))) := by
  -- `projOn S f` is fixed by translation by the `S.conjClosure`-part of a vector integral on
  -- `S.conjClosure`.
  have h_fix (a : p → 𝔸f E) (w : n₀ → 𝔸f E) (b : p → 𝔸f E)
      (h_int : a ∈ integralBox p S.conjClosure ∧ w ∈ integralBox n₀ S.conjClosure ∧
        b ∈ integralBox p S.conjClosure) :
      V.finHeisenbergOp (idem S.conjClosure • idem S.conjClosure • D.finFrameVector g t a w b)
        (V.projOn S f) = V.projOn S f :=
    V.finHeisenbergOp_projOn ((hg.finFrameVector_mem_integralBox a w b _).2 h_int) f
  simp only [boxIndicator, ite_smul, one_smul, zero_smul]
  split_ifs with hx
  · -- Translating by `(-x, y, 0)` removes the part of `x` on `S.conjClosure` and acts on the value
    -- by `y`. The mean over `y` is the projection.
    have h_translate (y : n₀ → 𝔸f E) (hy : y ∈ stdLattice E n₀) :
        T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.projOn S f)) = V₀.finHeisenbergOp
          (idem S.conjClosure • y)
          (T (t.val⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • x)) (V.ω g (V.projOn S f))) := by
      nth_rw 1 [← h_fix (-x) y 0 (by simp_all [integralBox, smul_mem_stdLattice])]
      simp [hT.apply_omega_rho_finFrameVector, ↓idem_compl, finHeisenbergOp, semichar,
        idem_mul_self,
        sub_smul, smul_smul, ← sub_eq_add_neg]
    exact (V₀.map_projOn_eq_const 1 fun y hy ↦ (h_translate y hy).symm).symm
  · -- Translating by `(0, 0, b)` multiplies the value by a character in `b`; if the value were not
    -- zero, the character would be trivial and `x` integral on `S.conjClosure`.
    have h_character (b : p → 𝔸f E) (hb : b ∈ stdLattice E p) :
        T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.projOn S f)) =
          (selfDualAddChar E (idem S.conjClosure * star b ⬝ᵥ x) : ℂ) •
            T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.projOn S f)) := by
      have h_half : half * idem S.conjClosure * star b ⬝ᵥ x +
          half * idem S.conjClosure * star b ⬝ᵥ x = idem S.conjClosure * star b ⬝ᵥ x := by grind
      nth_rw 1 [← h_fix 0 0 b (by simp_all [integralBox, smul_mem_stdLattice])]
      simp [hT.apply_omega_rho_finFrameVector, finHeisenbergOp, semichar, smul_smul, idem_mul_self,
        mul_add, ← mul_assoc, h_half]
    by_contra h_ne
    refine hx (mem_stdLattice_iff_selfDualAddChar.2 fun b hb ↦ smul_left_injective ℂ h_ne ?_)
    simpa using (h_character b hb).symm

/-- For a splitting `D` of `V` as `(l E^p ⊕ k E^p) ⊥ ι V₀`, a set `S` of finite places, `g` adapted
to `t` (`g⁻¹ (l (t⁻¹)ᴴ, k t, ι)` has orthonormal columns at every infinite place and integral finite
entries) and `T` obeying the law of a mixed Schrödinger model (`D.IsMixedLaw`), let `F = ω(g) P f`,
where `P = V.projOn S` is the mean of the finite Heisenberg operators over `Ô^n` above `S ∪ S̄` and
`S̄` is the set of conjugate places. For an adelic point `y`, the value `T (t⁻¹ᴴ y) F` vanishes
unless the finite coordinate `α⁻¹ y_f` (`New.finCoord`) is integral at every place of `S ∪ S̄`. In
that case it equals `V₀.projOn S (T (t⁻¹ᴴ y') F)`, where `y'` is `y` with its finite part above
`S ∪ S̄` removed. -/
lemma IsAdapted.omega_projOn_adelic_of_isMixedLaw {E : Type u_1} {n : Type u_2} {n₀ : Type u_3}
    {p : Type u_4} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
    [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s₀ : n₀ → ℤˣ} {V : Space E n s}
    {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p}
    {S : Set (FinPlace E)} {g : G E s} {t : GL p (𝔸 E)} {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀}
    (h_adapted : D.IsAdapted g t) (hT : D.IsMixedLaw T) (y : p → 𝔸 E) (f : 𝒮 V) :
    T (t.val⁻¹ᴴ *ᵥ y) (V.ω g (V.projOn S f)) =
      boxIndicator p S.conjClosure (finCoord y) •
        V₀.projOn S (T (t.val⁻¹ᴴ *ᵥ (y - finVec (idem S.conjClosure • finCoord y)))
          (V.ω g (V.projOn S f))) := by
  -- Split `y` into its real part `realVec a` and its finite part `finVec z`. The translation by
  -- the real part is moved into the vector as `ϱ r`, which commutes with `P`; then the case of a
  -- finite point, `IsAdapted.omega_projOn_of_isMixedLaw`, applies.
  set a : NumberField.InfinitePlace E × p → ℂ := realCoord y
  set z : p → 𝔸f E := finCoord y
  have h_split : y = realVec a + finVec z := by
    simpa [z, finVec, finCoord, funext_iff] using (realVec_realCoord_add y).symm
  let r : n → 𝔸 E := g⁻¹.adeleMatrix *ᵥ (D.lAdelic *ᵥ (t.val⁻¹ᴴ *ᵥ realVec a))
  have h_real : ∀ i : n, ∀ w ∈ S.conjClosure, (r i).2 w = 0 := by
    simp [r, Matrix.mulVec, dotProduct, realVec, snd_sum]
  have h_back : g.adeleMatrix *ᵥ r = D.lAdelic *ᵥ (t.val⁻¹ᴴ *ᵥ realVec a) := by
    simp [r, mulVec_mulVec, ← Matrix.mul_assoc, ← G.adeleMatrix_mul]
  have h_shift (x : p → 𝔸f E) :
      T (t.val⁻¹ᴴ *ᵥ (realVec a + finVec x)) (V.ω g (V.projOn S f)) =
        T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.projOn S (V.ϱ r f))) := by
    rw [projOn_rho _ h_real, omega_rho, h_back, hT.apply_rho_lAdelic_mulVec, mulVec_add, add_comm]
  have h_rest : y - finVec (idem S.conjClosure • z) =
      realVec a + finVec (idem S.conjClosureᶜ • z) := by
    rw [h_split, add_sub_assoc, idem_compl]
    simp [finVec, funext_iff, sub_mul, mul_sub]
  calc T (t.val⁻¹ᴴ *ᵥ y) (V.ω g (V.projOn S f))
    _ = T (t.val⁻¹ᴴ *ᵥ finVec z) (V.ω g (V.projOn S (V.ϱ r f))) := by rw [h_split, h_shift]
    _ = boxIndicator p S.conjClosure z • V₀.projOn S
          (T (t.val⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • z)) (V.ω g (V.projOn S (V.ϱ r f)))) :=
      h_adapted.omega_projOn_of_isMixedLaw hT z _
    _ = _ := by rw [h_rest, h_shift]

/-- Let `D` split `V` as `V₀ ⊥ (l E^p ⊕ k E^p)` via `ι`, let `g` be adapted to `t`
(`g⁻¹ (l (t⁻¹)ᴴ, k t, ι)` has orthonormal columns at every infinite place and integral finite
entries), and let `T` obey the mixed-model law `T x (ϱ y f) = β (2 x + a) b • ϱ w (T (x + a) f)` for
`y = l a + ι w + k b`. Then there is a constant `c` (possibly zero) such that for every adelic `x`,
`T x (ω(g) vacElem)` is `c * ‖vacuumFn (tᴴ x)‖ ^ 2` times the vacuum `vacElem` of `V₀`. Here
`vacElem` is the vacuum of `V` (Gaussian times twisted lattice indicator), and `vacuumFn y` is
`exp(−π ∑ Im(τȷ)|y_{i,τ}|²)` times `ψ_f(½c₀ȷ y_f*y_f)` when the finite part `y_f` lies in `αÔ^p`,
and `0` otherwise. -/
lemma IsAdapted.exists_omega_vacElem_of_isMixedLaw {E : Type u_1} {n : Type u_3} {n₀ : Type u_2}
    {p : Type u_4} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
    [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s₀ : n₀ → ℤˣ} {V : Space E n s}
    {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} {g : G E s} {t : GL p (𝔸 E)}
    {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀} (h_adapted : D.IsAdapted g t) (hT : D.IsMixedLaw T) :
    ∃ c : ℂ, ∀ x : p → 𝔸 E,
      T x (V.ω g V.vacElem) = (c * ‖vacuumFn (t.valᴴ *ᵥ x)‖ ^ 2) • V₀.vacElem := by
  -- Split `t.1ᴴ *ᵥ x` into a real part `a` and a finite part `z`. The real part contributes the
  -- Gaussian `exp (-|a|²)`, the finite part the indicator of the lattice, and the two vacuum
  -- projections together project onto the line of the vacuum.
  let u : 𝒮 V := V.ω g V.vacElem
  refine ⟨V₀.dataInner V₀.vacElem (T 0 u), fun x ↦ ?_⟩
  obtain ⟨⟨a, z⟩, haz⟩ := (adelicSum E 1).equiv.surjective (t.1ᴴ *ᵥ x)
  have h_sum : realVec a + finVec z = t.1ᴴ *ᵥ x := by simpa [realVec, finVec, funext_iff] using! haz
  have h_split : t.1⁻¹ᴴ *ᵥ realVec a + t.1⁻¹ᴴ *ᵥ finVec z = x := by
    simp [h_sum, ← mulVec_add, ← conjTranspose_mul]
  -- The vector `D.finFrameVector g t z 0 0` lies in the first block of the frame, spanned by the
  -- columns of g⁻¹ `D.l` t*⁻¹. By the law, the finite Heisenberg operator along it translates the
  -- argument of `T`.
  have h_shift (y : p → 𝔸 E) :
      T y (V.ω g (V.projReal (V.finHeisenbergOp (D.finFrameVector g t z 0 0) V.vacElem))) =
      T (y + t.1⁻¹ᴴ *ᵥ finVec z) u := by
    simp [u, hT, ↓integrated_finHeisenbergOp, finFrameVector, ↓star_dot_finFrameVector, omega_rho,
      finHeisenbergOp,
      semichar, frameAt, G.adeleMatrix, fromCols_map, ← mulVec_finVec]
  -- Real part: `omega_projReal_of_isMixedLaw` gives the Gaussian factor and the real vacuum
  -- projection.
  have h_real : T x u = exp (-(star a ⬝ᵥ a)) • V₀.projReal (T (t.1⁻¹ᴴ *ᵥ finVec z) u) := by
    rw [← h_split, ← h_shift, h_adapted.omega_projReal_of_isMixedLaw hT, h_shift, zero_add]
  -- Finite part: `omega_projOn_of_isMixedLaw` at all finite places gives the indicator of
  -- integrality.
  have h_fin : T (t.1⁻¹ᴴ *ᵥ finVec z) u =
      boxIndicator p (⊤ : Set (FinPlace E)).conjClosure z • V₀.projOn ⊤ (T 0 u) := by
    simpa [u, ↓idem_compl] using h_adapted.omega_projOn_of_isMixedLaw hT z V.vacElem (S := ⊤)
  -- The two projections together land on the line of the vacuum; the vacuum function at
  -- `t.1ᴴ *ᵥ x` is the product of its real and finite factors.
  have h_line : V₀.projReal (V₀.projOn Set.univ (T 0 u)) =
      V₀.dataInner V₀.vacElem (T 0 u) • V₀.vacElem := by
    simp [← dataInner_vacElem_smul_vacElem]
  rw [h_real, h_fin, ← haz, (adelicSum E 1).vac_equiv]
  by_cases hz : z ∈ stdLattice E p
  · simp [hz, stdLattice.finVac, sq, star_dotProduct_self_eq_sum, realVac, mul_comm (exp _),
    mul_assoc,
      integralBox, h_line, smul_smul, norm_exp, ← exp_add]
  · simp [hz, stdLattice.finVac, integralBox]

/-- Let `S` be disjoint from its conjugate `S̄`, `Ψ` Schwartz–Bruhat above `S` and `g` adapted to
`t`. The value of `ω(g) (Ψ ⊗ f)` at the finite point `x` is `Ψ_x ⊗` applied to the value of
`ω(g) P f` at the part of `x` off `S ∪ S̄`. Here `⊗` is `New.Space.schrodingerOp`, and
`P = V.projOn S` is the mean of the finite Heisenberg operators over `Ô^n` above `S ∪ S̄`.
`Ψ_x` (`sliceDatum`) is y ↦ ∫ ψ_f(ȷαᾱ x*b_S) Ψ(g⁻¹(l t*⁻¹x + ιy + ktb)) db over `b` integral off
`S`, with `α` the finite idele of the Weil data. The value at the finite point `x` means the value
of a map `T` obeying the law of a mixed model, taken at `t⁻¹ᴴ (α x)`. -/
lemma IsAdapted.omega_schrodingerOp_of_isMixedLaw
    {E : Type u_1} {n : Type u_2} {n₀ : Type u_3}
    {p : Type u_4} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
    [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s₀ : n₀ → ℤˣ} {V : Space E n s}
    {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} {S : Set (FinPlace E)}
    {g : G E s} {t : GL p (𝔸 E)} {Ψ : (n → 𝔸f E) → ℂ} {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀}
    (h : D.IsAdapted g t) (hT : D.IsMixedLaw T) (x : p → 𝔸f E) (f : 𝒮 V)
    (hS : S.IsConjDisjoint) (hΨ : IsSchwartzBruhat S Ψ) :
    T (t.val⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.schrodingerOp S Ψ f)) =
      V₀.schrodingerOp S (D.sliceDatum S g t Ψ x)
        (T (t.val⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • x)) (V.ω g (V.projOn S f))) := by
  classical
  -- Both sides are linear in `Ψ`, and `Ψ` is a combination of translates of the box function.
  obtain ⟨c, rfl⟩ : ∃ c : (n → 𝔸f E) →₀ ℂ,
      (∑ y ∈ c.support, c y • schrodingerAct S y (boxIndicator n S)) = Ψ :=
    mem_range_schrodingerCombination hS hΨ
  have h_lin : D.sliceDatum S g t (∑ y ∈ c.support, c y • schrodingerAct S y (boxIndicator n S)) x =
      ∑ y ∈ c.support, c y • D.sliceDatum S g t (schrodingerAct S y (boxIndicator n S)) x := by
    ext v
    simp only [sliceDatum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum,
      mul_left_comm (selfDualAddChar E _), ← integral_const_mul]
    refine integral_finsetSum _ fun y _ ↦ ?_
    -- Each integrand is a continuous function times a Schwartz–Bruhat function of `b`.
    simpa [finFrameVector, frameAt, fromCols_map, add_comm (_ *ᵥ x), add_assoc, mul_sum,
      mul_left_comm (selfDualAddChar E _), ← mul_assoc] using!
      (IsSchwartzBruhat.comp ((t⁻¹.1 * D.kCoord * g.adeleMatrix).map snd)
        (by simp [← coe_snd, G.adeleMatrix, Matrix.mul_assoc, ← Matrix.map_mul]) _).integrableOn_mul
        (by fun_prop)
  -- The datum of one translate: its integral is the Fourier transform of the box moved by `b`.
  have h_translate (a : p → 𝔸f E) (w : n₀ → 𝔸f E) (b : p → 𝔸f E) :
      D.sliceDatum S g t (schrodingerAct S (D.finFrameVector g t a w b) (boxIndicator n S)) x =
        selfDualAddChar E (half * star (idem S.conjClosure • b) ⬝ᵥ
          (x + (x + idem S.conjClosure • a))) •
          boxIndicator p S.conjClosure (x + idem S.conjClosure • a) •
            schrodingerAct S w (boxIndicator n₀ S) := by
    ext y
    rw [smul_comm]
    refine fourier_boxIndicator b _ _ fun b' ↦ ?_
    have h_add :
        D.finFrameVector g t x y b' + D.finFrameVector g t a w b =
          D.finFrameVector g t (x + a) (y + w) (b' + b) := by
      simp [finFrameVector, ← Sum.elim_add_add, ← mulVec_add]
    have h_idem : idem S * idem S.conjClosure = idem S := by
      grind [idem_mul_self, idem_conjClosure_eq_add_star, idem_mul_star]
    -- By `finFrameVector_mem_integralBox` the two integrands have the same support.
    simp [schrodingerAct, h_add, h.finFrameVector_mem_integralBox, ite_and, mul_add,
      ← mul_assoc, idem_mul_self, ← AddChar.map_add_eq_mul]
    simp [h_idem, integralBox, smul_smul]
    congr! 3
    -- The phases differ by a trace `τ + star τ`, which `selfDualAddChar` does not see.
    apply selfDualAddChar_congr (half * idem S * star (x + x + a) ⬝ᵥ b) (zero_mem _)
    simp [mul_add]
    grind [star_dotProduct, idem_mul_self, idem_conjClosure_eq_add_star, idem_mul_star]
  have h_off (a : p → 𝔸f E) :
      idem S.conjClosureᶜ • (x + idem S.conjClosure • a) = idem S.conjClosureᶜ • x := by
    have h_zero : idem S.conjClosureᶜ * idem S.conjClosure = 0 := by
      simp [↓idem_compl, sub_mul, idem_mul_self]
    rw [smul_add, smul_smul, h_zero, zero_smul, add_zero]
  rw [h_lin]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    schrodingerOp_schrodingerAct_boxIndicator hS]
  congr! with y
  obtain ⟨a, w, b, rfl⟩ := D.exists_eq_finFrameVector g t y
  -- For one translate use `apply_omega_rho_finFrameVector` on the left, then
  -- `omega_projOn_of_isMixedLaw` at `x + idem S.conjClosure • a`.
  rw [h_translate, smul_finFrameVector, hT.apply_omega_rho_finFrameVector,
    h.omega_projOn_of_isMixedLaw hT (x + _), h_off, map_smul,
      ← schrodingerOp_schrodingerAct_boxIndicator hS,
    smul_schrodingerOp, smul_schrodingerOp]

end MixedModelNames

/-!
## Sums over rational points, θ as a sum of slices, and the slices of the vacuum

* `New.Space.Splitting.exists_tsum_slice_le`: a bound on `∑_ξ ‖f[φ ξ]‖` along any additive map
  `φ`. The bound is `#(φ⁻¹B) · M · ‖f‖`, with a compact `B` and a constant `M` that are independent
  of `φ` and `f`; it may be infinite.
-/

section RationalSums

open Matrix IsDualFamily NumberField Heisenberg.IsVacuum ContinuousLinearMap

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ} {n₀ p : Type*} [Fintype n₀]
  [DecidableEq n₀] [Fintype p] [DecidableEq p] {s₀ : n₀ → ℤˣ} {V : Space E n s}
  {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} (f : 𝒮 V)

/-- There are a compact B in 𝔸^p and M such that, for every additive group homomorphism φ into 𝔸^p
and every f in 𝒮(V), ∑_ξ ‖f[φ(ξ)]‖ ≤ #(φ⁻¹B) · M · ‖f‖, where f[x] is the mixed model along the
splitting D. -/
lemma exists_tsum_slice_le :
    ∃ B : Set (p → 𝔸 E), IsCompact B ∧
      ∃ M : NNReal, ∀ {ι : Type _} [AddGroup ι] (φ : ι →+ (p → 𝔸 E)) (f : 𝒮 V),
        ∑' ξ : ι, ‖D.slice (φ ξ) f‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖f‖ₑ := by
  -- Wiener's bound needs one vector u with u(0) ≠ 0 whose translates along l have, under
  -- `D.zeroTerm`, the norms of translates of an integrable function. Take u = ω(g) vac with g
  -- adapted to 1: then `D.slice x u` = c |`vacuumFn x`|² vac, which is integrable in x.
  obtain ⟨g, hg, -⟩ := D.exists_isAdapted_and_frame_eq 1
  obtain ⟨c, hc⟩ := hg.exists_omega_vacElem_of_isMixedLaw D.isMixedLaw_slice
  have h_int : MeasureTheory.Integrable
      (fun x : p → 𝔸 E ↦ (c * (‖vacuumFn x‖ ^ 2 : ℝ)) • V₀.vacElem) vacuumMeasure :=
    ((integrable_norm_sq (stdSpace E p).vacElem).ofReal.const_mul c).smul_const V₀.vacElem
  let κ : (p → 𝔸 E) →L[𝔸 E] n → 𝔸 E := ⟨D.lAdelic.toLin', (toLin' _).continuous_on_pi⟩
  have h_norm (z : n → 𝔸 E) (x : p → 𝔸 E) :
      ‖D.zeroTerm (V.ϱ (z + D.lAdelic *ᵥ x) (V.ω g V.vacElem))‖ₑ =
        ‖(c * (‖vacuumFn (D.lCoord *ᵥ z + x)‖ ^ 2 : ℝ)) • V₀.vacElem‖ₑ := by
    rw [← slice_zero, isMixedLaw_slice, hc]
    simp [← ofReal_norm, norm_smul, mulVec_add, Heisenberg.norm_eq_one, Heisenberg.Rep.norm_map]
  -- `( :)`: `V.ϱ` is by definition the Heisenberg operator of the model.
  exact (wiener_bound D.zeroTerm (right_ne_zero_of_mul_eq_one (conj_delta_mul_weilRep_vacElem _ g))
    κ h_int D.lCoord.mulVec (by simpa [κ, vacElem] using! h_norm) :)

/-- There is M such that ∑_{ξ ∈ E^p} ‖f[ξ]‖ ≤ M‖f‖ for all f in 𝒮(V). -/
lemma tsum_enorm_slice_le :
    ∃ M : NNReal, ∀ f : 𝒮 V, ∑' ξ : p → E, ‖D.slice (toAdele ∘ ξ) f‖ₑ ≤ M * ‖f‖ₑ := by
  -- The compact set `B` contains only finitely many rational vectors.
  obtain ⟨B, hB, M, hM⟩ := D.exists_tsum_slice_le
  let φ : (p → E) →+ p → 𝔸 E := (toAdele (E := E)).toAddMonoidHom.compLeft p
  have h_fin : (φ ⁻¹' B).Finite := isCovolOneLattice_ratVectors.finite_preimage hB
  exact ⟨(φ ⁻¹' B).ncard * M, fun f ↦ by simpa [← h_fin.cast_ncard_eq] using! hM φ f⟩

lemma summable_norm_slice : Summable fun ξ : p → E ↦ ‖D.slice (toAdele ∘ ξ) f‖ := by
  obtain ⟨M, hM⟩ := D.tsum_enorm_slice_le
  exact (ENNReal.summable_toReal ((hM f).trans_lt (by finiteness)).ne :)

/-- For a splitting `D` of `V` as `(l E^p ⊕ k E^p) ⊥ ι V₀` and f in 𝒮(V), the family θ_{V₀}(f[ξ]), ξ
in E^p, is summable with sum θ_V(f). Here f[ξ] = `D.slice ξ f` in 𝒮(V₀) is the zero term along `k`
of ϱ(lξ)f. -/
lemma hasSum_theta_slice :
    HasSum (fun x : p → E ↦ V₀.θ (D.slice (toAdele ∘ x) f)) (V.θ f) := by
  -- Fourier inversion at 0 for the periodic function b ↦ f(k b) on 𝔸^p: the numbers
  -- θ(`D.slice ξ f`) are its Fourier coefficients for the characters b ↦ β(b, ξ)².
  have h_dual : IsDualFamily (New.ratVectors E p) fun ξ b ↦
      (adelicHeisenberg E 1).β b ((stdSpace E p).vecAtPoint ξ) ^ 2 := by
    convert (stdSpace E p).isDualFamily_beta_sq
    ext
    simp [mem_ratVectors_iff]
  have h_coeff (ξ : p → E) : V₀.θ (D.slice (toAdele ∘ ξ) f) =
      quotMean (New.ratVectors E p) fun b : p → 𝔸 E ↦
        (adelicHeisenberg E 1).β b ((stdSpace E p).vecAtPoint ξ) ^ 2 *
          f (D.iAdelic *ᵥ 0 + D.kAdelic *ᵥ b) := by
    -- The theta functional of V₀ is evaluation at 0.
    change D.zeroTerm (V.ϱ (D.lAdelic *ᵥ (toAdele ∘ ξ)) f) 0 = _
    rw [zeroTerm_apply]
    congr! with b
    -- Commute ϱ(l ξ) past ϱ(k b); the commutator is the character, and θ absorbs ϱ(l ξ).
    rw [← theta_rho, theta_eq_rawTheta, rho_swap, map_smul]
    erw [V.isThetaFunctional_rawTheta.left _ (D.symm.kAdelic_mulVec_mem_ratVectors ⟨ξ, rfl⟩)]
    simp [D.beta_eq_coords, vecAtPoint]
    -- The rest is the definition of evaluation: `θ (ϱ(k b) f) = f (k b)`.
    rfl
  simpa using fourier_inversion (D.isContPeriodic_along_k f 0)
    (V₀.θ.summable (D.summable_norm_slice f).of_norm) h_coeff 0

/-- For a Witt decomposition `D` of `V` as `(l E^p ⊕ k E^p) ⊥ ι V₀` over a CM field `E` with Weil
data, the zero term along `k` is not the zero map. This zero term is the bounded map 𝒮(V) → 𝒮(V₀)
sending `f` to `y ↦` the mean of `θ(ϱ(ιy + kb) f)` over `b` in 𝔸^p modulo E^p. -/
lemma zeroTerm_ne_zero : D.zeroTerm ≠ 0 := by
  -- If the zero term vanished, so would all slices, and `θ` is the sum of the `θ` of the slices.
  intro h_zero
  have h_theta (f : 𝒮 V) : V.θ f = 0 := by
    simpa [slice, h_zero] using (D.hasSum_theta_slice f).tsum_eq.symm
  have h_vac : V.vacElem = 0 := by
    ext y
    simpa [theta_rho] using h_theta (V.ϱ y V.vacElem)
  simpa [h_vac] using V.dataInner_vacElem_vacElem

/-- Let `D` be a Witt decomposition `V = (l E^p ⊕ k E^p) ⊥ ι V₀` over a CM field `E` with Weil data.
Suppose `g` is adapted to `t` (`New.Space.Splitting.IsAdapted`): the columns of
`g⁻¹ (l (t⁻¹)ᴴ, k t, ι)` are orthonormal at every infinite place and have integral finite entries.
Then for `f = ω(g) vacElem` there is `c ≠ 0` such that, for every `x` in 𝔸^p, the slice (mixed
model) of `f` at `x` is `c * ‖vacuumFn (tᴴ x)‖ ^ 2` times the vacuum of `V₀`, where `vacuumFn` is
the standard adelic vacuum (Gaussian at the infinite places, twisted lattice indicator at the finite
places). -/
lemma IsAdapted.slice_omega_vacElem {g : G E s} {t : GL p (𝔸 E)} (h_adapted : D.IsAdapted g t) :
    ∃ c ≠ (0 : ℂ), ∀ x : p → 𝔸 E,
      D.slice x (V.ω g V.vacElem) = (c * ‖vacuumFn (t.valᴴ *ᵥ x)‖ ^ 2) • V₀.vacElem := by
  obtain ⟨c, hc⟩ := h_adapted.exists_omega_vacElem_of_isMixedLaw D.isMixedLaw_slice
  refine ⟨c, fun hc₀ ↦ ?_, hc⟩
  -- If c = 0, the law of the mixed model makes the zero term vanish on all translates of ω(g) vac,
  -- and so everywhere.
  refine D.zeroTerm_ne_zero (V.ext_of_vacElem g fun y ↦ ?_)
  rw [← slice_zero, omega_rho, isMixedLaw_slice, hc, hc₀]
  simp

/-- The mixed model as an integral. Let `g` be adapted to `t`, and for an adelic vector `y` write
`g y = l a + ι w + k b`. There is `c ≠ 0` such that, for all `f` and `x`, the value `(ω(g) f)[x]`
is `c` times the integral over `y` of the coefficient `⟨ϱ(y) vac, f⟩`, times
`β (2 x + a) b * ‖vacuumFn (tᴴ (x + a))‖ ^ 2`, times the translate by `w` of the vacuum of `V₀`.
Here `β` is the bicharacter of `adelicHeisenberg E 1`. The middle factor is the value at `x` of the
translate by `l a + k b` of the function `‖vacuumFn (tᴴ ·)‖ ^ 2` in the Schrödinger model. -/
lemma IsAdapted.slice_omega_eq_integral {g : G E s} {t : GL p (𝔸 E)}
    (h_adapted : D.IsAdapted g t) :
    ∃ c ≠ (0 : ℂ), ∀ (f : 𝒮 V) (x : p → 𝔸 E),
      D.slice x (V.ω g f) = c • ∫ y : n → 𝔸 E,
        (V.dataInner (V.ϱ y V.vacElem) f *
          ((adelicHeisenberg E 1).β (x + (x + D.lCoord *ᵥ g.adeleMatrix *ᵥ y))
            (D.kCoord *ᵥ g.adeleMatrix *ᵥ y) *
            ‖vacuumFn (t.valᴴ *ᵥ (x + D.lCoord *ᵥ g.adeleMatrix *ᵥ y))‖ ^ 2)) •
          V₀.ϱ (D.iCoord *ᵥ g.adeleMatrix *ᵥ y) V₀.vacElem ∂vacuumMeasure := by
  -- By superposition it suffices to know the mixed model of the translates `ω(g) ϱ(y) vac`; it
  -- comes from the law of the mixed model and the values at `ω(g) vac`.
  obtain ⟨c, hc_ne, hc⟩ := h_adapted.slice_omega_vacElem
  refine ⟨c, hc_ne, fun f x ↦ ?_⟩
  have h_translate (y : n → 𝔸 E) : D.slice x (V.ω g (V.ϱ y V.vacElem)) =
      (c * ((adelicHeisenberg E 1).β (x + (x + D.lCoord *ᵥ g.adeleMatrix *ᵥ y))
        (D.kCoord *ᵥ g.adeleMatrix *ᵥ y) *
        ‖vacuumFn (t.valᴴ *ᵥ (x + D.lCoord *ᵥ g.adeleMatrix *ᵥ y))‖ ^ 2)) •
        V₀.ϱ (D.iCoord *ᵥ g.adeleMatrix *ᵥ y) V₀.vacElem := by
    rw [omega_rho, isMixedLaw_slice, hc, map_smul, smul_smul, mul_left_comm]
  calc D.slice x (V.ω g f)
    _ = ∫ y : n → 𝔸 E, V.dataInner (V.ϱ y V.vacElem) f •
          D.slice x (V.ω g (V.ϱ y V.vacElem)) ∂vacuumMeasure :=
      V.map_eq_integral_dataInner f (D.slice x ∘L V.ω g)
    _ = _ := by
      rw [← MeasureTheory.integral_smul]
      congr with y : 1
      rw [h_translate, smul_smul, smul_smul, mul_left_comm]

end RationalSums

end New.Space.Splitting

end
