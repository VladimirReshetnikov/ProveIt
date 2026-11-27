import Lib.Adelic.Unitary.GramMatrix

/-!
# Closed matrix embedding of adelic unitary groups, discrete rational points, weak approximation

This file concerns the adelic unitary group `New.G E s = G_∞ × G_f` over a CM field `E` (hypothesis
`IsCMField E`; the discreteness instance and the `New.Space` results assume `CMType E` instead,
which makes `E` a CM field), together with the rational points of a hermitian space `V` with signs
`s`. When all signs are `1`, the finite parts of the rational points form a discrete subgroup of
`G_f`.

## Main definitions and results

* `New.G.isClosedEmbedding_adeleMatrix`: sending `g` to its adelic matrix is a closed embedding.
  Hence a map into the group is continuous when its matrix is (`New.G.continuous_iff`), and elements
  with the same matrix are equal (`New.G.ext_adeleMatrix`).
* An instance: for a space `W` whose signs are all `1`, the group `New.Space.Γf` of finite parts of
  the rational points is discrete in `G_f`.
* `New.Space.cayleyMap`: a map from all rational matrices to the rational points, through the Cayley
  transform of a rational skew matrix.
* `New.Space.eventually_tendsto_cayleyMap`: for all but finitely many parameters `c`, the image of
  `A` under this map tends to `g` at a given place as `A + e • B` (`A` rational, `B` adelic) tends
  to `V.toRatCoords g`, if the place kills the adeles `e` and `star e`.
* `New.Space.weak_approximation`: weak approximation. The consequence that a rational translate of a
  finite adelic point is integral above a prime is `New.exists_mul_mem_integralAbove`, in
  `Lib.Adelic.AutomorphicForms.PAdicGauge`.

Notions from other files:
* `New.G E s`: the adelic unitary group for the signs `s`; `New.G.adeleMatrix g` is the `n × n`
  matrix over the adeles of its element `g`.
* `New.Space E n s`: a hermitian space with a point, given by a matrix `J` over `E` and `x` in
  `GL_n(𝔸)` with `xᴴ J x` equal to `diag s` at the infinite places and `1` at the finite places.
* `New.Space.ratEmbed`, `New.Space.embFin`: `γ ↦ x⁻¹ γ x` from the rational unitary group of `J` to
  `G`, and its finite part; their images are `New.Space.Γ` and `New.Space.Γf`.
* `New.Space.toRatCoords`: `g ↦ x g x⁻¹` from `G` to the adelic unitary group of `J`.

## Relation to the literature

Known result: weak approximation for unitary groups. Source: V. Platonov, A. Rapinchuk, Algebraic
Groups and Number Theory, 1994, ch. 7. Here a hermitian space comes with an adelic frame to a fixed
diagonal form, and this form is the identity at all finite places, so every space of one signature
shares one adelic group.
-/

/-! ## Closed embedding into matrices and discreteness of rational points -/

namespace New

open NumberField Topology U

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n]
  [DecidableEq n] {s : n → ℤˣ}

/-- Sending an element of the adelic unitary group to its adelic matrix is a closed embedding. -/
lemma G.isClosedEmbedding_adeleMatrix : IsClosedEmbedding
  (adeleMatrix : G E s → Matrix n n (𝔸 E)) := by
  -- `adeleMatrix` is `toUnitary` followed by the closed embedding of the unitary group of
  -- `stdForm E s` into matrices, so it suffices that `toUnitary` and its inverse are continuous.
  have h_emb : IsClosedEmbedding fun u : U (stdForm E s) ↦ (u.val : Matrix n n (𝔸 E)) :=
    U.isClosedEmbedding_coe isUnit_stdForm
  have h_symm : Continuous (toUnitary.symm : U (stdForm E s) → G E s) :=
    .prodMk (continuous_pi fun w ↦ continuous_map (continuous_apply w).fst')
      (continuous_map continuous_snd)
  exact h_emb.comp
    (toUnitary.left_inv.isClosedEmbedding h_symm (h_emb.continuous_iff.2 continuous_adeleMatrix))

/-- Elements of the adelic unitary group with the same adelic matrix are equal. -/
lemma G.ext_adeleMatrix {g g' : G E s} (h : g.adeleMatrix = g'.adeleMatrix) : g = g' :=
  isClosedEmbedding_adeleMatrix.injective h

/-- A map into the adelic unitary group is continuous if and only if its adelic matrix is. -/
lemma G.continuous_iff {X : Type*} [TopologicalSpace X] {f : X → G E s} :
    Continuous f ↔ Continuous fun x : X ↦ (f x).adeleMatrix :=
  isClosedEmbedding_adeleMatrix.continuous_iff

/-- For a space `W` whose signs are all `1`, the finite parts of the rational points form a
discrete subgroup `W.Γf` of `G_f`. -/
instance {E : Type*} [Field E] [CMType E] (W : Space E n 1) : DiscreteTopology W.Γf := by
  -- The rational points are discrete in `G E 1`, so a compact set holds only finitely many.
  have h_emb : Filter.Tendsto W.ratEmbed .cofinite (.cocompact (G E 1)) :=
    W.ratEmbed.tendsto_coe_cofinite_of_isDiscrete W.ratEmbed_injective ⟨W.discreteTopology_Gamma⟩
  -- All signs are `1`, so the infinite part of `G E 1` is compact and can be dropped.
  have h_fin : Filter.Tendsto (fun γ : U W.J ↦ (W.ratEmbed γ).2) .cofinite
    (.cocompact (Gf E n)) := by
    simpa [← Filter.coprod_cocompact, Function.comp_def] using h_emb
  -- `W.Γf` is the range of `W.embFin γ = (W.ratEmbed γ).2`.
  refine continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
    (.mono_left ?_ (Set.rangeFactorization_surjective (f := W.embFin)).le_map_cofinite)
  exact h_fin

end New

/-!
## Weak approximation at infinity and finitely many finite places

Let `x` be the point of `V`. Then `V.toRatCoords g = x g x⁻¹` and `V.ratEmbed γ = x⁻¹ γ x`
translate between `New.G` and the unitary group of `V.J`.

The idea: let `γ = V.toRatCoords g` and take a rational `c` with `star c * c = 1` and `1 + c γ`
invertible at the given places. The Cayley transform of `c γ` is skew for `V.J`, rational skew
matrices `u` approach it, and the rational isometries `c⁻¹ (1 - u) (1 + u)⁻¹` approach `γ`; so
their images under `V.ratEmbed` approach `g`. The matrices `u` come from rational matrices that
approach `γ` (`New.Exchange.denseRange_rat_matrix_add`).
-/

namespace New.Space

open Matrix Topology Filter G Exchange Function Gf RingHom Algebra

variable {E n : Type*} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  (V : Space E n s)

/-- A CM field has infinitely many elements `c` with `star c * c = 1`. -/
instance : Infinite (unitary E) := by
  -- For `z ≠ star z`, the quotients `star y / y` with `y = k + z`, `k : ℕ`, are pairwise distinct.
  obtain ⟨z, hz⟩ : ∃ z : E, IsUnit (z - star z) := exists_isUnit_sub_star
  -- `1 - (y - star y) * y⁻¹` is `star y / y` for `y ≠ 0` and `1` for `y = 0`.
  have h_mem (y : E) : 1 - (y - star y) * y⁻¹ ∈ unitary E := by
    suffices h : (1 - (star y - y) * (star y)⁻¹) * (1 - (y - star y) * y⁻¹) = 1 by
      simpa [unitary, mul_comm] using h
    grind [star_eq_zero]
  refine .of_injective (fun k : ℕ ↦ ⟨_, h_mem (k + z)⟩) fun k l hkl ↦ ?_
  -- The difference `y - star y = z - star z` is nonzero and does not depend on `k`.
  simpa [hz.ne_zero] using hkl

/-- The Cayley transform `(1 - A) (1 + A)⁻¹` of a square matrix (`0` if `1 + A` is singular). -/
noncomputable def _root_.New.cayleyTransform {K : Type*} [Field K] (A : Matrix n n K) :
    Matrix n n K :=
  (1 - A) * (1 + A)⁻¹

/-- The Cayley transform is an involution where it is defined: if `2 ≠ 0` in `K` and `1 + A` is
invertible and `C` is the transform of `A`, then `1 + C` is invertible and the transform of `C` is
`A`. -/
lemma _root_.New.cayleyTransform_cayleyTransform {K : Type*} [Field K] (h_two : (2 : K) ≠ 0)
    {A : Matrix n n K} (hA : (1 + A).det ≠ 0) :
    (1 + cayleyTransform A).det ≠ 0 ∧ cayleyTransform (cayleyTransform A) = A := by
  -- `(1 + C) (1 + A) = 2` and `(1 - C) (1 + A) = 2 A`.
  have h_cancel : cayleyTransform A * (1 + A) = 1 - A := by simp [cayleyTransform, hA]
  have h_add : (1 + cayleyTransform A) * ((2 : K)⁻¹ • (1 + A)) = 1 := by
    rw [mul_smul_comm, one_add_mul, h_cancel, inv_smul_eq_iff₀ h_two, two_smul, add_add_sub_cancel]
  have h_sub : (1 - cayleyTransform A) * ((2 : K)⁻¹ • (1 + A)) = A := by
    rw [mul_smul_comm, one_sub_mul, h_cancel, inv_smul_eq_iff₀ h_two, two_smul, add_sub_sub_cancel]
  exact ⟨(isUnit_det_of_right_inverse h_add).ne_zero,
    by rw [cayleyTransform, inv_eq_right_inv h_add, h_sub]⟩

/-- The two factors of the Cayley transform commute. -/
lemma _root_.New.cayleyTransform_eq_inv_mul {K : Type*} [Field K] (A : Matrix n n K) :
    cayleyTransform A = (1 + A)⁻¹ * (1 - A) := by
  have h_comm : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by noncomm_ring
  obtain hA | hA := eq_or_ne (1 + A).det 0
  · simp [cayleyTransform, inv_def, hA]
  · calc _ = (1 + A)⁻¹ * ((1 + A) * (1 - A)) * (1 + A)⁻¹ := by simp [cayleyTransform, hA]
      _ = (1 + A)⁻¹ * (1 - A) := by simp [h_comm, Matrix.mul_assoc, hA]

/-- The Cayley transform of an isometry is skew. Here `B` stands for the conjugate transpose of
`A`: if `B J A = J` with `J` and `1 + A` invertible, then `1 + B` is invertible and the
transforms `A'`, `B'` satisfy `B' J = -J A'`. -/
lemma _root_.New.cayleyTransform_mul_eq_neg {K : Type*} [Field K] {A B J : Matrix n n K}
    (h_gram : B * J * A = J) (hJ : J.det ≠ 0) (hA : (1 + A).det ≠ 0) :
    (1 + B).det ≠ 0 ∧ cayleyTransform B * J = -(J * cayleyTransform A) := by
  have h_add : (1 + B) * J * A = J * (1 + A) := by simp [add_mul, mul_add, h_gram, add_comm]
  have hB : (1 + B).det ≠ 0 := fun h_zero ↦ by simpa [h_zero, hJ, hA] using congrArg det h_add
  -- Both sides of `h_cross` are `J A - B J`.
  have h_cross : (1 - B) * J * (1 + A) = -((1 + B) * J * (1 - A)) := by
    simp only [sub_mul, add_mul, mul_add, mul_sub, h_gram, one_mul, mul_one]
    abel
  refine ⟨hB, ?_⟩
  calc _ = (1 + B)⁻¹ * ((1 - B) * J * (1 + A)) * (1 + A)⁻¹ := by
        simp [cayleyTransform_eq_inv_mul, ← Matrix.mul_assoc, hA]
    _ = -(J * cayleyTransform A) := by simp [h_cross, cayleyTransform, Matrix.mul_assoc, hB]

/-- Inversion of matrices commutes with maps of fields. -/
lemma _root_.New.map_nonsing_inv {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (A : Matrix n n K) : A⁻¹.map φ = (A.map φ)⁻¹ := by
  have h_adj : A.adjugate.map φ = (A.map φ).adjugate := φ.map_adjugate A
  simp [inv_def, map_smul' φ _ _ φ.map_mul, φ.map_det, h_adj]

/-- The Cayley transform commutes with maps of fields. -/
lemma _root_.New.cayleyTransform_map {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (A : Matrix n n K) : (cayleyTransform A).map φ = cayleyTransform (A.map φ) := by
  simp [cayleyTransform, map_nonsing_inv, Matrix.map_add, Matrix.map_sub]

/-- The Cayley transform is continuous where `1 + A` is invertible. -/
lemma _root_.New.continuousAt_cayleyTransform {K : Type*} [NormedField K] {A : Matrix n n K}
    (hA : (1 + A).det ≠ 0) : ContinuousAt cayleyTransform A := by
  have h_eq : (cayleyTransform : Matrix n n K → Matrix n n K) =
      fun X ↦ (1 - X) * ((1 + X).det⁻¹ • (1 + X).adjugate) := by
    ext1 X
    simp [cayleyTransform, inv_def]
  rw [h_eq]
  fun_prop (disch := exact hA)

/-- The part of a rational matrix `C` that is skew for the form `J = V.J`, namely
`(C - J⁻¹ Cᴴ J) / 2`. -/
noncomputable def formSkewPart (C : Matrix n n E) : Matrix n n E :=
  (2 : E)⁻¹ • (C - V.J⁻¹ * Cᴴ * V.J)

/-- The skew part `u` of a matrix satisfies `uᴴ J = -J u`. -/
lemma conjTranspose_formSkewPart_mul (C : Matrix n n E) :
    (V.formSkewPart C)ᴴ * V.J = -(V.J * V.formSkewPart C) := by
  have hJ : V.J.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 V.isUnit_J).ne_zero
  simp [formSkewPart, conjTranspose_nonsing_inv, conjTranspose_J, mul_assoc, mul_sub, sub_mul,
    smul_sub, hJ]

/-- If `u` is skew for the form of `V`, `1 + u` is invertible and `star c * c = 1`, then `c⁻¹` times
the Cayley transform of `u` is an isometry of `V`. -/
lemma smul_cayleyTransform_isometry (c : unitary E) {u : Matrix n n E}
    (hu : uᴴ * V.J = -(V.J * u)) (h_det : (1 + u).det ≠ 0) :
    (c.1⁻¹ • cayleyTransform u)ᴴ * V.J * (c.1⁻¹ • cayleyTransform u) = V.J := by
  -- `(1 - u)ᴴ J (1 - u) = (1 + u)ᴴ J (1 + u)`; multiply by the inverse of `1 + u` on both sides.
  have h_gram : (1 - u)ᴴ * V.J * (1 - u) = (1 + u)ᴴ * V.J * (1 + u) := by
    simp only [conjTranspose_sub, conjTranspose_add, conjTranspose_one, sub_mul, add_mul, hu]
    noncomm_ring
  have hc : c.1⁻¹ * star c.1⁻¹ = 1 := by simp [← mul_inv]
  calc _ = (c.1⁻¹ * star c.1⁻¹) • ((1 + u)⁻¹ᴴ * ((1 - u)ᴴ * V.J * (1 - u)) * (1 + u)⁻¹) := by
        simp [cayleyTransform, smul_smul, Matrix.mul_assoc]
    _ = ((1 + u) * (1 + u)⁻¹)ᴴ * V.J * ((1 + u) * (1 + u)⁻¹) := by
        simp only [hc, h_gram, one_smul, conjTranspose_mul, Matrix.mul_assoc]
    _ = V.J := by simp [h_det]

open scoped Classical in
/-- A map from rational matrices to rational points of the space `V`. For `star c * c = 1` and a
square matrix `A` over `E`, let `u` be the skew part of the Cayley transform of `c A`. The value is
the image under `V.ratEmbed` of the isometry `c⁻¹ (1 - u) (1 + u)⁻¹` of `V.J` if `1 + u` is
invertible, and `1` otherwise. -/
noncomputable def cayleyMap (c : unitary E) (A : Matrix n n E) : G E s :=
  let u : Matrix n n E := V.formSkewPart (cayleyTransform (c.1 • A))
  V.ratEmbed (if h : (1 + u).det ≠ 0 then
    U.of V.isUnit_J (c.1⁻¹ • cayleyTransform u)
      (V.smul_cayleyTransform_isometry c (V.conjTranspose_formSkewPart_mul _) h)
  else 1)

/-- Let `V` be a hermitian space over the CM field `E`: a matrix `J` with a point `x` in `GL_n(𝔸)`
such that `xᴴ J x` is `diag s` at the infinite places and `1` at the finite places. Let `f` be a
continuous ring map from the adeles to a normed field that kills both the adele `e` and `star e`.
Then for all but finitely many `c` in `E` with `star c * c = 1`, the following holds: when
`A + e • B` tends to `V.toRatCoords g = x g x⁻¹`, with `A` rational (embedded diagonally by
`toAdele`) and `B` adelic, the adelic matrix of the rational point `V.cayleyMap c A` tends to that
of `g` after applying `f`. Here `V.cayleyMap c A` is `x⁻¹ c⁻¹ (1 - u) (1 + u)⁻¹ x`, where `u` is the
skew part of the Cayley transform of `c A`, and it is `1` if `1 + u` is not invertible. -/
lemma eventually_tendsto_cayleyMap (g : G E s) (e : 𝔸 E) {K : Type*} [NormedField K]
    (f : 𝔸 E →+* K) (hf : Continuous f) (hf_zero : f e = 0 ∧ f (star e) = 0) :
    ∀ᶠ c : unitary E in cofinite,
      Tendsto (fun p : Matrix n n E × Matrix n n (𝔸 E) ↦ (V.cayleyMap c p.1).adeleMatrix.map f)
        (comap (fun p : Matrix n n E × Matrix n n (𝔸 E) ↦ p.1.map toAdele + e • p.2)
          (𝓝 (V.toRatCoords g)))
        (𝓝 (g.adeleMatrix.map f)) := by
  -- Let `γ = V.toRatCoords g`, read through `f`, and take `c` with `1 + c γ` invertible. The Cayley
  -- transform `C` of `c γ` is skew, so the rational skew matrices `u` of `cayleyMap` tend to `C`,
  -- and `c⁻¹ (1 - u) (1 + u)⁻¹` tends to `γ`.
  let φ : E →+* K := f.comp toAdele
  let γ : Matrix n n (𝔸 E) := V.toRatCoords g
  have off_spectrum : ∀ᶠ c : unitary E in cofinite, -(φ c)⁻¹ ∉ spectrum K (γ.map f) :=
    ((neg_injective.comp inv_injective).comp
      (φ.injective.comp Subtype.val_injective)).tendsto_cofinite.eventually
      (γ.map f).finite_spectrum.eventually_cofinite_notMem
  filter_upwards [off_spectrum] with c hc
  have h_norm : φ (star c.1) * φ c = 1 := by rw [← map_mul, c.prop.left, map_one]
  have hc_ne : φ c ≠ 0 := right_ne_zero_of_mul_eq_one h_norm
  have h_two : (2 : K) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero φ).2 two_ne_zero
  let J : Matrix n n K := V.J.map φ
  have hJ : J.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (V.isUnit_J.map φ.mapMatrix)).ne_zero
  have h_det : (1 + φ c • γ.map f).det ≠ 0 := by
    have h_eq : 1 + φ c • γ.map f = -φ c • (algebraMap K _ (-(φ c)⁻¹) - γ.map f) := by
      simp [algebraMap_eq_smul_one, smul_sub, smul_smul, hc_ne]
    rw [h_eq, det_smul]
    simpa [hc_ne, isUnit_iff_isUnit_det] using spectrum.notMem_iff.1 hc
  let C : Matrix n n K := cayleyTransform (φ c • γ.map f)
  -- `v A` is the rational skew matrix in the definition of `V.cayleyMap c A`.
  let v (A : Matrix n n E) : Matrix n n E := V.formSkewPart (cayleyTransform (c.1 • A))
  -- As `f` need not respect conjugation, the images of `A` and `Aᴴ` are two variables `x`, `y`.
  let u (x y : Matrix n n K) : Matrix n n K :=
    (2 : K)⁻¹ • (cayleyTransform (φ c • x) - J⁻¹ * cayleyTransform (φ (star c.1) • y) * J)
  have h_u (A : Matrix n n E) : (v A).map φ = u (A.map φ) (Aᴴ.map φ) := by
    have h_star : (cayleyTransform (c.1 • A))ᴴ = cayleyTransform (star c.1 • Aᴴ) := by
      rw [cayleyTransform_eq_inv_mul (star c.1 • Aᴴ)]
      simp [cayleyTransform, conjTranspose_nonsing_inv]
    simp [u, v, J, formSkewPart, h_star, map_nonsing_inv, map_smul', Matrix.map_sub, Matrix.map_mul,
      cayleyTransform_map, map_ofNat]
  have gram : φ (star c.1) • γᴴ.map f * J * φ c • γ.map f = J := by
    have h_gram : γᴴ.map f * J * γ.map f = J := by
      simpa [J, φ, γ, coe_comp] using congrArg (map · f) (V.toRatCoords g).prop
    simp [smul_smul, mul_comm (φ c), h_norm, h_gram]
  obtain ⟨h_det_star, skew⟩ := cayleyTransform_mul_eq_neg gram hJ h_det
  have u_value : u (γ.map f) (γᴴ.map f) = C := by
    simp [u, C, Matrix.mul_assoc, skew, hJ, ← two_smul K, smul_smul, h_two]
  obtain ⟨h_back, h_invol⟩ : (1 + C).det ≠ 0 ∧ cayleyTransform C = φ c • γ.map f :=
    cayleyTransform_cayleyTransform h_two h_det
  have h_cont (A : Matrix n n K) (hA : (1 + A).det ≠ 0) : ContinuousAt cayleyTransform A :=
    continuousAt_cayleyTransform hA
  -- The rational skew matrices tend to `C`; `f` kills `e` and `star e`, so it does not see `B`.
  have u_cont : ContinuousAt (fun x : Matrix n n (𝔸 E) ↦ u (x.map f) (xᴴ.map f)) γ := by
    fun_prop (disch := assumption)
  have u_tendsto : Tendsto (fun p : Matrix n n E × Matrix n n (𝔸 E) ↦ (v p.1).map φ)
      (comap (fun p ↦ p.1.map toAdele + e • p.2) (𝓝 γ)) (𝓝 C) := by
    rw [← u_value]
    refine (u_cont.tendsto.comp tendsto_comap).congr fun p ↦ ?_
    rw [h_u]
    simp [φ, conjTranspose_map_toAdele, map_smul', Matrix.map_add, hf_zero, coe_comp]
  -- Near `C` the matrix `1 + u` is invertible and the Cayley transform is continuous.
  let Ψ (x : Matrix n n K) : Matrix n n K :=
    V.x⁻¹.val.map f * (φ c)⁻¹ • cayleyTransform x * V.x.val.map f
  have value : Ψ C = g.adeleMatrix.map f := by
    simp [Ψ, h_invol, hc_ne, γ, mul_assoc, ← Matrix.map_mul, toRatCoords, adeleMatrix]
  have Ψ_cont : ContinuousAt Ψ C := by fun_prop (disch := assumption)
  have h_near : ∀ᶠ x in 𝓝 C, (1 + x).det ≠ 0 := ContinuousAt.eventually_ne (by fun_prop) h_back
  rw [← value]
  refine (Ψ_cont.tendsto.comp u_tendsto).congr' ((u_tendsto.eventually h_near).mono fun p hp ↦ ?_)
  have h_rat : (1 + v p.1).det ≠ 0 := by rwa [← map_ne_zero φ, φ.map_det, map_add, map_one]
  have h_map : (φ c)⁻¹ • cayleyTransform ((v p.1).map φ) =
      (c.1⁻¹ • cayleyTransform (v p.1)).map φ := by simp [cayleyTransform_map, map_smul']
  simp only [Function.comp_apply, Ψ, v, h_map, cayleyMap, dite_eq_left h_rat, adeleMatrix_ratEmbed,
    Matrix.map_mul]
  rfl

/-- For a finite set `T` of finite places, multiplying a finite adele `y` by the idempotent
`idem T` (component `1` on `T` and `0` elsewhere) gives the sum over `w ∈ T` of the adeles
`singleAdele w (evalAt w y)` with component `evalAt w y = y w` at `w` and `0` elsewhere. -/
lemma _root_.New.idem_mul_eq_sum_singleAdele {T : Set (FinPlace E)} (hT : T.Finite) (y : 𝔸f E) :
    idem T * y = ∑ w ∈ hT.toFinset, singleAdele w (evalAt w y) := by
  classical
  refine DFunLike.ext _ _ fun u ↦ ?_
  change evalAt u (idem T * y) = evalAt u (∑ w ∈ hT.toFinset, singleAdele w (evalAt w y))
  have h_single (w : FinPlace E) : singleAdele w (y w) u = if u = w then y u else 0 := by
    obtain rfl | h := eq_or_ne u w <;> simp [*]
  simp [h_single, idem_apply]

/-- Convergence in `G` from convergence place by place: for an adele `a`, `a.1 w` is its component
at an infinite place and `evalAt w a.2` at a finite one. If the matrices of `x i` tend to the
matrix of `g` at every infinite place and at every place of the finite set `S` or conjugate to
one (`S.conjClosure`), then `x i` tends to `g` once the components at all other finite places are
replaced by `1` (`componentOn n S`). -/
lemma _root_.New.G.tendsto_componentOn {S : Set (FinPlace E)} (hS : S.Finite) {ι : Type*}
    {l : Filter ι} {x : ι → G E s} {g : G E s}
    (h_inf : ∀ w : NumberField.InfinitePlace E,
      Tendsto (fun i : ι ↦ (x i).adeleMatrix.map fun a : 𝔸 E ↦ a.1 w) l
        (𝓝 (g.adeleMatrix.map fun a : 𝔸 E ↦ a.1 w)))
    (h_fin : ∀ w ∈ S.conjClosure,
      Tendsto (fun i : ι ↦ (x i).adeleMatrix.map fun a : 𝔸 E ↦ evalAt w a.2) l
        (𝓝 (g.adeleMatrix.map fun a : 𝔸 E ↦ evalAt w a.2))) :
    Tendsto (fun i : ι ↦ ((x i).1, componentOn n S (x i).2) : ι → G E s) l
      (𝓝 (g.1, componentOn n S g.2)) := by
  -- Matrices converge entry by entry. An entry converges at each infinite place by `h_inf`; its
  -- finite part is cut down to the finitely many places of `S.conjClosure`, where `h_fin` applies.
  let e : 𝔸f E := idem S.conjClosure
  have h_entry_inf (j k : n) : Tendsto (fun i : ι ↦ ((x i).adeleMatrix j k).1) l
    (𝓝 (g.adeleMatrix j k).1) :=
    tendsto_pi_nhds.2 fun w ↦ ((h_inf w).apply_nhds j).apply_nhds k
  have h_entry_fin (j k : n) :
      Tendsto (fun i : ι ↦ e * ((x i).adeleMatrix j k).2) l (𝓝 (e * (g.adeleMatrix j k).2)) := by
    simp only [e, idem_mul_eq_sum_singleAdele hS.conjClosure]
    refine tendsto_finsetSum _ fun w hw ↦ ((continuous_singleAdele w).tendsto _).comp ?_
    exact ((h_fin w (hS.conjClosure.mem_toFinset.1 hw)).apply_nhds j).apply_nhds k
  rw [isClosedEmbedding_adeleMatrix.tendsto_nhds_iff]
  refine tendsto_pi_nhds.2 fun j ↦ tendsto_pi_nhds.2 fun k ↦ ?_
  -- By definition `componentOn n S` is `m ↦ e • m + (1 - e) • 1`.
  let b : 𝔸f E := ((1 - e) • 1 : Matrix n n (𝔸f E)) j k
  change Tendsto (fun i : ι ↦ (((x i).adeleMatrix j k).1, e * ((x i).adeleMatrix j k).2 + b)) l
    (𝓝 ((g.adeleMatrix j k).1, e * (g.adeleMatrix j k).2 + b))
  exact (h_entry_inf j k).prodMk_nhds ((h_entry_fin j k).add_const b)

/-- Weak approximation. For a finite set `S` of finite places, the products `γ * (1, h)` are dense
in the adelic unitary group `G = G_∞ × G_f`, where `γ` runs over the rational points `V.Γ` and
`h` over the elements of `G_f` with component `1` at every place of `S`. So `V.Γ` is dense at
infinity and at the places of `S`. -/
lemma weak_approximation {S : Set (FinPlace E)} (hS : S.Finite) :
    DenseRange fun p : V.Γ × trivialOn n S ↦ (p.1 : G E s) * (1, (p.2 : Gf E n)) := by
  -- By strong approximation, rational matrices `A` approach `V.toRatCoords g` at infinity and on
  -- `S.conjClosure`, the places of `S` and their conjugates (along the filter `l`). For a suitable
  -- `c` the rational points `V.cayleyMap c A` then tend to `g` at these places by
  -- `eventually_tendsto_cayleyMap`; an element of `trivialOn n S` corrects the other components.
  intro g
  let e : 𝔸 E := idemAdele S.conjClosureᶜ
  let approx (p : Matrix n n E × Matrix n n (𝔸 E)) : Matrix n n (𝔸 E) := p.1.map toAdele + e • p.2
  let l : Filter (Matrix n n E × Matrix n n (𝔸 E)) := comap approx (𝓝 (V.toRatCoords g))
  have h_dense : DenseRange approx := by
    simpa [approx, e] using denseRange_rat_matrix_add hS.conjClosure.infinite_compl.nonempty
      (1 : GL n (𝔸 E))
  have : l.NeBot := comap_neBot fun _ ↦ h_dense.mem_nhds
  -- At each infinite place and each place of `S.conjClosure`, where `e` vanishes, all but
  -- finitely many `c` give convergence along `l`; take one `c` for all of them.
  have at_infinite : ∀ᶠ c : unitary E in cofinite, ∀ w : NumberField.InfinitePlace E,
      Tendsto (fun p ↦ (V.cayleyMap c p.1).adeleMatrix.map fun a ↦ a.1 w) l
        (𝓝 (g.adeleMatrix.map fun a ↦ a.1 w)) :=
    eventually_all.2 fun w ↦ V.eventually_tendsto_cayleyMap g e
      ((Pi.evalRingHom _ w).comp (fst _ _)) (continuous_apply w).fst' (by simp [e])
  have at_finite : ∀ᶠ c : unitary E in cofinite, ∀ w ∈ S.conjClosure,
      Tendsto (fun p ↦ (V.cayleyMap c p.1).adeleMatrix.map fun a ↦ evalAt w a.2) l
        (𝓝 (g.adeleMatrix.map fun a ↦ evalAt w a.2)) :=
    (eventually_all_finite hS.conjClosure).2 fun w hw ↦ V.eventually_tendsto_cayleyMap g e
      ((evalAt w).comp (snd _ _)) (continuous_evalAt w).snd' (by aesop (add norm simp e))
  obtain ⟨c, h_inf, h_fin⟩ := (at_infinite.and at_finite).exists
  -- `π` keeps the components at infinity and on `S.conjClosure` and replaces the others by `1`.
  let π : G E s →* G E s := (MonoidHom.id _).prodMap (componentOn n S)
  have h_tendsto : Tendsto (fun p ↦ π (V.cayleyMap c p.1)) l (𝓝 (π g)) :=
    tendsto_componentOn hS h_inf h_fin
  -- `g = π g * ((π g)⁻¹ * g)` is the limit of `π x * ((π g)⁻¹ * g)`, `x = V.cayleyMap c A`; this
  -- differs from `x` only at finite places outside `S.conjClosure`.
  rw [← mul_inv_cancel_left (π g) g]
  refine mem_closure_of_tendsto (h_tendsto.mul_const _) (.of_forall fun p ↦ ?_)
  set x : G E s := V.cayleyMap c p.1
  let h : Gf E n := (x⁻¹ * (π x * ((π g)⁻¹ * g))).2
  have h_triv : h ∈ trivialOn n S := by simp +contextual [h, π, atPlace_componentOn, trivialOn]
  have h_eq : x * (1, h) = π x * ((π g)⁻¹ * g) := Prod.ext (by simp [π]) (by simp [h])
  -- `cayleyMap` is by definition in the range `V.Γ` of `V.ratEmbed`.
  exact ⟨(⟨x, _, rfl⟩, ⟨h, h_triv⟩), h_eq⟩

end New.Space
