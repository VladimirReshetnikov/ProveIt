import Lib.Adelic.Reduction.FiniteVolume
import Lib.Shimura.AbelianScheme.Basic
import Lib.Shimura.Transfer.MarkedPairs

/-!
# Trace formula for algebraic forms, finiteness of signed frame classes, the definite side

This file gives a trace formula for a Hecke operator on a finite-dimensional space of algebraic
forms, computed from class representatives with weights. It also shows that only finitely many
double cosets GL_n(E) x (GU ∩ V), with V an open subgroup, contain a signed frame. These results
serve the definite side of the comparison of traces. There the trace of a regular Hecke element on
forms supported on definite frames is written as a sum over orbits of triples.

## Main definitions and results

* `New.trace_eq_weighted_sum`: the trace of the twisted Hecke operator `T` on a finite-dimensional
  space of algebraic forms, from representatives `r i` with weights `w i`.
* `New.Variety.finite_isSignedFrame_classes`: for an open subgroup V, only finitely many double
  cosets GL_n(E) x (GU ∩ V) contain a signed frame.
* `New.Variety.definiteForms`: the forms with values in a representation `ξ` of `GL n E` that
  are left `GL n E`-equivariant, vanish off the definite frames and are right invariant under the
  level.
* `New.Variety.definiteForms.rep`: the action of the Hecke algebra `New.Variety.heckeAlgebra` on it.
* `New.Variety.finite_definiteForms`, `New.Variety.finite_support_countTerm_definite`,
  `New.Variety.trace_definiteForms_eq_finsum_countTerm`: finite dimension, finite support and the
  trace formula.

Notions from other files:
* `New.levelSpace π K`: The vectors fixed by the subgroup `K` under the representation `π`; here
  `π` is `New.rightRegular`, the action of `G` on functions `G → W` by right translation.
* `New.Variety.GU`: The unitary similitudes: the `g ∈ GL_n(𝔸f E)` with `c • gᴴ g = ε • 1` for some
  rational `c > 0` and unit `ε` of `Ẑ`, that is, the frames of the forms `c • 1`.
* `New.Variety.levelGU`: the principal level K(𝔑), the similitudes in `GL_n(Ô E)` that are congruent
  to `1` modulo `𝔑`.
* `New.Variety.IsRegularHecke`: a(x⁻¹y⁻¹xK) ≠ 0 forces the characteristic polynomial of `y` to
  be separable.
* `New.Variety.IsNeat`: The level 𝔑 is neat: 𝔑 ≠ 0 and, whenever `x` is a signed frame with `ℓ` for
  some form (`New.Variety.IsSignedFrame`), every y in GL_n(E) with x⁻¹yx in `levelGU n 𝔑` that fixes
  ℓ under `New.Variety.ratConj` equals 1.

## Relation to the literature

Known; see `Lib.Shimura.TraceFormula.MarkedDefiniteSums` and
`Lib.Shimura.Uniformisation.AppellHumbert` for sources.
-/

noncomputable section

/-!
## Trace of a Hecke operator from weighted class representatives

The identity of a space `M` of equivariant forms is written as a weighted sum of maps that factor
through `W` by evaluation at representatives `r i`; the trace then moves over to `W`.
-/

section TraceFormula

open Function LinearMap New Finset Variety

/-- Let `S g` be finite sets of elements of `Γ` with `γ ∈ S g ↔ g⁻¹ * (e γ * r) ∈ K`, empty for
`g ∈ D`. Then for every `v ∈ W` the function `g ↦ ∑ γ ∈ S g, ρ γ v` is equivariant along `e`
(it lies in `ρ.coindV e`), vanishes on `D` and is right `K`-invariant. -/
private lemma New.pi_sum_apply_mem_coindV_inf_levelSpace {A G Γ W : Type*} [Field A] [Group G]
    [Group Γ] [AddCommGroup W] [Module A W] {e : Γ →* G} {ρ : Representation A Γ W}
    {K : Subgroup G} {D : Set G} (r : G) (S : G → Finset Γ)
    (h_mem_S : ∀ (g : G) (γ : Γ), γ ∈ S g ↔ g⁻¹ * (e γ * r) ∈ K) (h_empty : ∀ g ∈ D, S g = ∅)
    (v : W) :
    LinearMap.pi (fun g : G ↦ ∑ γ ∈ S g, ρ γ) v ∈
      ρ.coindV e ⊓ Submodule.pi D ⊥ ⊓ levelSpace (rightRegular A G W) K := by
  -- equivariance: multiplication by `γ⁻¹` matches `S (e γ * g)` with `S g`
  have equivariant (γ : Γ) (g : G) : ∑ δ ∈ S (e γ * g), ρ δ v = ∑ δ ∈ S g, ρ γ (ρ δ v) :=
    Finset.sum_equiv (.mulLeft γ⁻¹) (by simp [h_mem_S, mul_assoc]) (by simp)
  have invariant (k : K) (g : G) : S (g * k) = S g := by
    ext γ
    simp [h_mem_S, mul_assoc, mul_mem_cancel_left]
  refine ⟨⟨fun γ g ↦ ?_, fun g hg ↦ ?_⟩, fun k ↦ funext fun g ↦ ?_⟩
  · simpa using equivariant γ g
  · simp [h_empty g hg]
  · simp [invariant]

/-- The trace of one term of the trace formula `New.trace_eq_weighted_sum`. Let `J : W → M` be
linear with `ι (J v) g = ∑ γ ∈ S g, ρ γ v`, where `γ ∈ S g ↔ g⁻¹ * (e γ * r) ∈ K`; let `σ` be an
automorphism of `G` preserving `K`, and let `T` send `F` to the right translate of `s ∘ F ∘ σ⁻¹` by
the group ring element `a`. Then the trace of `T ∘ J ∘ (F ↦ F r) ∘ ι` on `M` is `∑ᶠ γ, cosetFn K a
(r⁻¹ * σ (e γ) * σ r) * trace (s * ρ γ)`. Here `cosetFn K a x` is the sum of the coefficients `a g`
over the `g` with `g K = x K`. -/
private lemma New.trace_mul_comp_proj_comp_eq_finsum_cosetFn {A G Γ W M : Type*} [Field A]
    [Group G] [Group Γ] [AddCommGroup W] [Module A W] [Module.Finite A W] [AddCommGroup M]
    [Module A M] [Module.Finite A M] {e : Γ →* G} {ρ : Representation A Γ W} {K : Subgroup G}
    (ι : M →ₗ[A] G → W) (r : G) (S : G → Finset Γ)
    (h_mem_S : ∀ (g : G) (γ : Γ), γ ∈ S g ↔ g⁻¹ * (e γ * r) ∈ K)
    (σ : G ≃* G) (hσ : K.comap (σ : G →* G) = K)
    {s : Module.End A W} {a : MonoidAlgebra A G} {T : Module.End A M}
    (hT : ∀ ψ : M,
      ι (T ψ) = (rightRegular A G W).asAlgebraHom a fun g : G ↦ s (ι ψ (σ.symm g)))
    (J : W →ₗ[A] M) (ι_J : ∀ (v : W) (g : G), ι (J v) g = ∑ γ ∈ S g, ρ γ v) :
    trace A M (T * J ∘ₗ proj r ∘ₗ ι) =
      ∑ᶠ γ : Γ, cosetFn K a (r⁻¹ * σ (e γ) * σ r) * trace A W (s * ρ γ) := by
  classical
  -- Moved over to `W`, the map is `v ↦ ι (T (J v)) r`, which `hT` computes.
  let S' (g : G) : Finset Γ := S (σ.symm (r * g))
  have on_W :
      (proj r ∘ₗ ι) ∘ₗ T ∘ₗ J = ∑ g ∈ a.coeff.support, ∑ γ ∈ S' g, a.coeff g • (s * ρ γ) := by
    ext v
    simp [hT, ι_J, S', asAlgebraHom_eq_sum_support, smul_sum]
  -- `γ` occurs in `S' g` exactly for the `g` of one coset, as `σ` preserves `K`.
  have mem_S' (γ : Γ) (g : G) : γ ∈ S' g ↔ (g : G ⧸ K) = (r⁻¹ * σ (e γ) * σ r : G) := by
    rw [h_mem_S, ← hσ, Subgroup.mem_comap, hσ]
    simp [QuotientGroup.eq, mul_assoc]
  calc
    trace A M ((T ∘ₗ J) ∘ₗ proj r ∘ₗ ι) = trace A W ((proj r ∘ₗ ι) ∘ₗ T ∘ₗ J) :=
      trace_comp_comm' _ _
    _ = ∑ x ∈ a.coeff.support.sigma S', a.coeff x.fst * trace A W (s * ρ x.snd) := by
      simp [on_W, sum_sigma]
    _ = ∑ᶠ γ : Γ, cosetFn K a (r⁻¹ * σ (e γ) * σ r) * trace A W (s * ρ γ) := by
      -- group the pairs `(g, γ)` by `γ`
      rw [← finsum_sum_filter fun x ↦ x.snd]
      refine finsum_congr fun γ ↦ ?_
      simp +contextual [sum_filter, sum_sigma, mem_S', cosetFn, asAlgebraHom_eq_sum_support,
        sum_mul, Finsupp.single_apply]

/-- Let `ι` identify `M` with the `F : G → W` with `F (e γ * g) = ρ γ (F g)`, zero on `D` and right
`K`-invariant; `T` sends `F` to the right translate of `s ∘ F ∘ σ⁻¹` by `a`, and `σ` preserves `K`.
For points `r i` of `G` and weights `w i` such that `S i g = {γ | e γ * r i ∈ g K}` is empty on `D`
and `∑ i, w i * #(S i g) = 1` off `D`, `M` is finite-dimensional and `tr T` is the sum over `i` of
`w i * ∑ᶠ γ, cosetFn K a ((r i)⁻¹ * σ (e γ) * σ (r i)) * tr (s * ρ γ)`; `cosetFn` = `∑ a_g [gK]`. -/
lemma New.trace_eq_weighted_sum {A G Γ W M I : Type*} [Field A] [Group G] [Group Γ]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [AddCommGroup M] [Module A M] [Fintype I]
    {e : Γ →* G} {ρ : Representation A Γ W} {K : Subgroup G} {D : Set G}
    (ι : M →ₗ[A] G → W) (hι_injective : Injective ι)
    (hι_range : ι.range = ρ.coindV e ⊓ Submodule.pi D ⊥ ⊓ levelSpace (rightRegular A G W) K)
    (r : I → G) (w : I → A) (S : I → G → Finset Γ)
    (h_mem_S : ∀ (i : I) (g : G) (γ : Γ), γ ∈ S i g ↔ g⁻¹ * (e γ * r i) ∈ K)
    (h_empty : ∀ g ∈ D, ∀ i : I, S i g = ∅)
    (h_count : ∀ g ∉ D, ∑ i : I, w i * #(S i g) = 1)
    (σ : G ≃* G) (hσ : K.comap (σ : G →* G) = K)
    {s : Module.End A W} {a : MonoidAlgebra A G} {T : Module.End A M}
    (hT : ∀ ψ : M,
      ι (T ψ) = (rightRegular A G W).asAlgebraHom a fun g : G ↦ s (ι ψ (σ.symm g))) :
    Module.Finite A M ∧
    trace A M T =
      ∑ i : I, w i *
        ∑ᶠ γ : Γ, cosetFn K a ((r i)⁻¹ * σ (e γ) * σ (r i)) * trace A W (s * ρ γ) := by
  classical
  -- For `v : W` the function `g ↦ ∑ γ ∈ S i g, ρ γ v` lies in `M`; call it `J i v`. The maps
  -- `ψ ↦ J i (ι ψ (r i))`, weighted by `w i`, add up to the identity of `M`. So `M` is a quotient
  -- of `I → W`, and the trace of `T` is a weighted sum of traces that can be moved over to `W`.
  have mem_range (i : I) (v : W) : pi (fun g ↦ ∑ γ ∈ S i g, ρ γ) v ∈ ι.range :=
    hι_range.ge (pi_sum_apply_mem_coindV_inf_levelSpace (r i) (S i) (h_mem_S i)
      (fun g hg ↦ h_empty g hg i) v)
  let J (i : I) : W →ₗ[A] M :=
    codRestrictOfInjective (pi fun g ↦ ∑ γ ∈ S i g, ρ γ) ι hι_injective (mem_range i)
  have ι_J (i : I) (v : W) (g : G) : ι (J i v) g = ∑ γ ∈ S i g, ρ γ v := by simp [J]
  have sum_J (ψ : M) : ∑ i, w i • J i (ι ψ (r i)) = ψ := by
    refine hι_injective (funext fun g ↦ ?_)
    obtain ⟨⟨equivariant, vanishes⟩, invariant⟩ := hι_range.le (mem_range_self ι ψ)
    -- Each `γ ∈ S i g` contributes `ρ γ (ι ψ (r i)) = ι ψ (e γ * r i) = ι ψ g`.
    have h_rho_apply_eq (i : I) (γ : Γ) (hγ : γ ∈ S i g) : ρ γ (ι ψ (r i)) = ι ψ g := by
      rw [← equivariant]
      -- right invariance under `k = g⁻¹ * (e γ * r i)`, evaluated at `g`
      simpa using congrFun (invariant ⟨g⁻¹ * (e γ * r i), (h_mem_S i g γ).mp hγ⟩) g
    calc
      ι (∑ i, w i • J i (ι ψ (r i))) g = (∑ i, w i * #(S i g)) • ι ψ g := by
        simp +contextual [ι_J, h_rho_apply_eq, sum_smul, mul_smul, Nat.cast_smul_eq_nsmul]
      _ = ι ψ g := by
        by_cases hg : g ∈ D
        · rw [show ι ψ g = 0 from vanishes g hg, smul_zero]
        · rw [h_count g hg, one_smul]
  have h_finite : Module.Finite A M :=
    .of_surjective (lsum A (fun _ : I ↦ W) A J) fun ψ ↦
      ⟨fun i ↦ w i • ι ψ (r i), by simpa using sum_J ψ⟩
  have T_eq : T = ∑ i, w i • (T * J i ∘ₗ proj (r i) ∘ₗ ι) := by
    ext ψ
    simpa using congrArg T (sum_J ψ).symm
  have trace_T : trace A M T = ∑ i, w i * trace A M (T * J i ∘ₗ proj (r i) ∘ₗ ι) := by
    conv_lhs => rw [T_eq]
    simp
  refine ⟨h_finite, trace_T.trans (sum_congr rfl fun i _ ↦ ?_)⟩
  rw [trace_mul_comp_proj_comp_eq_finsum_cosetFn ι (r i) (S i) (h_mem_S i) σ hσ hT (J i) (ι_J i)]

end TraceFormula

/-!
## Finiteness of double cosets carrying signed frames

An element `x` is a frame for a rational matrix β (`New.Variety.IsFrameFor`) if xᴴ β x is a unit of
Ẑ times the identity. `New.Variety.IsSignedFrame x ℓ` asks for such a β that is positive definite at
all infinite places other than the base place v₀ given by `CMBase E`, and such that β ℓ is positive
definite at v₀.
-/

section FiniteClasses

open Matrix ComplexOrder QuotientGroup Units DoubleCoset Set New.Core

/-- An invertible self-adjoint complex matrix `B` is congruent to a unitary one: for
`a = √|B⁻¹|`, built by the continuous functional calculus, the matrix `aᴴ B a` is unitary. -/
lemma New.Variety.exists_star_mul_mul_mem_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (B : GL n ℂ) (hB : IsSelfAdjoint B.val) :
    ∃ a : GL n ℂ, (star a * B * a).val ∈ unitary (Matrix n n ℂ) := by
  -- The spectrum of `B` is finite, real and misses `0`, so every function on it is continuous, and
  -- `aᴴ B a` is the function `x / |x| = ±1` of `B`.
  have h_sq_one : ∀ x ∈ spectrum ℝ B.val,
      star (√|x⁻¹| * x * √|x⁻¹|) * (√|x⁻¹| * x * √|x⁻¹|) = 1 := by
    grind [star_trivial, zero_notMem_spectrum]
  have h_root_ne_zero : ∀ x ∈ spectrum ℝ B.val, √|x⁻¹| ≠ 0 := by grind [zero_notMem_spectrum]
  let a : GL n ℂ := cfcUnits (fun x : ℝ ↦ √|x⁻¹|) B h_root_ne_zero
  -- `a` is self-adjoint, so `aᴴ B a` is the function `√|x⁻¹| * x * √|x⁻¹|` of `B`.
  have h_conj_eq : (star a * B * a).val = cfc (fun x : ℝ ↦ √|x⁻¹| * x * √|x⁻¹|) B.val := by
    simp [a, star_trivial, cfc_mul, cfc_id', ← cfc_star, finite_real_spectrum.continuousOn, hB]
  exact ⟨a, by rwa [h_conj_eq, cfc_unitary_iff _ B.val]⟩

/-- There is a compact set `B` of adelic matrices such that every frame `x` for an invertible
rational form `J` (that is, `xᴴ J x` is a unit of `Ẑ` times `1`) can be completed by archimedean
components `a` to an adelic matrix `g = (a, x)` whose Gram matrix `gᴴ J g` lies in `B`. -/
private lemma New.Variety.exists_isCompact_gram_mkAdelicGL_mem (E n : Type) [Field E] [CMBase E]
    [Fintype n] [DecidableEq n] :
    ∃ B : Set (GL n (𝔸 E)), IsCompact B ∧
      ∀ (J : GL n E) (x : GL n (𝔸f E)), IsFrameFor J.val x →
        ∃ a : NumberField.InfinitePlace E → GL n ℂ,
          star (mkAdelicGL (a, x)) * .map toAdele J * mkAdelicGL (a, x) ∈ B := by
  -- `B` consists of the `g` such that `g` and `g⁻¹` have entries that are integral and of norm at
  -- most `1` at infinity.
  let box : Set (Matrix n n (𝔸 E)) :=
    (Metric.closedBall (0 : NumberField.InfinitePlace E → ℂ) 1 ×ˢ (Ô E : Set (𝔸f E))).matrix
  have h_box : IsCompact box := isCompact_closedBall_prod_integral.matrix
  refine ⟨embedProduct (Matrix n n (𝔸 E)) ⁻¹' (box ×ˢ (MulOpposite.op '' box)),
    isClosedEmbedding_embedProduct.isCompact_preimage
      (h_box.prod (h_box.image_of_continuous MulOpposite.op)), fun J x h_frame ↦ ?_⟩
  -- Choose `a` making `J` unitary. The Gram matrix is then unitary at infinity and a unit scalar
  -- at the finite places.
  have h_unitary (w : NumberField.InfinitePlace E) :
      ∃ a : GL n ℂ, star a.val * J.val.map (Φ w) * a.val ∈ unitary (Matrix n n ℂ) := by
    simpa using exists_star_mul_mul_mem_unitary (.map (Φ w) J) h_frame.isHermitian_map
  choose a ha using h_unitary
  obtain ⟨ν, hν⟩ : ∃ ν : (Ô ℚ)ˣ,
      x.valᴴ * J.val.map (algebraMap E (𝔸f E)) * x.val = finAdeleIncl ℚ E ν • 1 := h_frame
  have h_gram : star (mkAdelicGL (a, x)) * .map toAdele J * mkAdelicGL (a, x) =
      mkAdelicGL (fun w ↦ Unitary.toUnits ⟨_, ha w⟩,
        ν.map ((finAdeleIncl ℚ E).domRestrict (Ô ℚ)).toMonoidHom • 1) := by
    refine ext (matrix_ext_𝔸 (fun w ↦ ?_) ?_)
    · push_cast [Matrix.map_mul]
      rfl
    · push_cast [Matrix.map_mul]
      exact hν
  use a
  rw [h_gram]
  simp [box, matrix, ← map_inv, entry_norm_bound_of_unitary, ha, ite_mem,
    pi_norm_le_iff_of_nonneg, smul_def, Matrix.one_apply]

/-- If `r` and `y` are frames for the same rational form `β` and lie in one coset of `V`, then
`r` and `Y y`, for `Y` in `GL_n(E)`, lie in one double coset `GL_n(E) r (GU E n ⊓ V)`. -/
private lemma New.Variety.doubleCoset_mk_eq_of_isFrameFor {E n : Type} [Field E] [CMBase E]
    [Fintype n] [DecidableEq n] {V : Subgroup (GL n (𝔸f E))} {β : Matrix n n E}
    {r y : GL n (𝔸f E)} (hr : IsFrameFor β r) (hy : IsFrameFor β y)
    (h_coset : (r : GL n (𝔸f E) ⧸ V) = (y : GL n (𝔸f E) ⧸ V)) (Y : GL n E) :
    DoubleCoset.mk toFinGL.range (GU E n ⊓ V) r =
      DoubleCoset.mk toFinGL.range (GU E n ⊓ V) (toFinGL Y * y) := by
  have h_GU : r⁻¹ * y ∈ GU E n := ⟨1, one_pos, hr.mul_iff.mp (by simpa using hy)⟩
  have h_V : r⁻¹ * y ∈ V := QuotientGroup.eq.mp h_coset
  exact (DoubleCoset.eq ..).mpr ⟨toFinGL Y, ⟨Y, rfl⟩, r⁻¹ * y, ⟨h_GU, h_V⟩, by simp [mul_assoc]⟩

/-- Let `V` be an open subgroup of `GL_n(𝔸f E)`. The elements `x` that are signed frames for some
complex matrix `ℓ` (`New.Variety.IsSignedFrame`: `x` is a frame for some form `β` over `E` with
positivity conditions) lie in finitely many double cosets `GL_n(E) x (GU E n ⊓ V)`. Here `GU E n` is
the unitary similitudes `g` with `gᴴ g` a scalar finite idele of `ℚ`, and `GL_n(E)` acts on the left
through its diagonal embedding `toFinGL`. -/
lemma New.Variety.finite_isSignedFrame_classes {E n : Type} [Field E] [CMBase E] [Fintype n]
    [DecidableEq n] {V : Subgroup (GL n (𝔸f E))} (hV : V.IsOpen) :
    (DoubleCoset.mk toFinGL.range (GU E n ⊓ V) ''
      {x : GL n (𝔸f E) | ∃ ℓ : Matrix n n ℂ, IsSignedFrame x ℓ}).Finite := by
  -- Mahler's criterion moves a frame by a rational matrix so that its form lies in a finite set
  -- `F`, and the frame lies in a compact set, which meets finitely many cosets of `V`. Two frames
  -- for one form in one coset of `V` differ by an element of `GU E n ⊓ V`. `rep β q` is a frame
  -- for `β` in the coset `q`, if there is one.
  let rep (β : Matrix n n E) (q : GL n (𝔸f E) ⧸ V) : GL n (𝔸f E) :=
    Classical.epsilon fun x : GL n (𝔸f E) ↦ IsFrameFor β x ∧ (x : GL n (𝔸f E) ⧸ V) = q
  obtain ⟨B, hB, h_gram_mem⟩ := exists_isCompact_gram_mkAdelicGL_mem E n
  obtain ⟨F, C, Cf, hF, -, hCf, h_mahler⟩ := exists_isBoundedDualBasis hB
  refine (hF.image2 (fun β q ↦ ⟦rep β q⟧) (finite_quotient_image_of_isCompact hV hCf)).subset ?_
  -- `x` is a signed frame for the rational form `J₀`
  rintro _ ⟨x, ⟨_ℓ, J₀, h_frame, h_sig⟩, rfl⟩
  -- The form `J₀` is positive definite at a place `v ≠ v₀`, so it is an invertible matrix `J`.
  obtain ⟨v, hv⟩ : ∃ v : NumberField.InfinitePlace E, v ≠ v₀ := exists_ne v₀
  have h_pos : (J₀.map (Φ v)).PosDef := by simpa [hv] using h_sig v
  obtain ⟨J, rfl⟩ : IsUnit J₀ := isUnit_of_mapMatrix _ h_pos.isUnit
  -- Mahler's criterion applies to the adelic frame `g = (a, x)`, whose Gram matrix lies in `B`.
  obtain ⟨a, ha⟩ := h_gram_mem J x h_frame
  let g : GL n (𝔸 E) := mkAdelicGL (a, x)
  obtain ⟨Z, s, hZ⟩ : ∃ (Z : GL n E) (s : Finset n), IsBoundedDualBasis F C Cf J g Z s :=
    h_mahler J g ha
  -- As `Zᴴ J Z` is positive definite at `v`, no vector of `Z` is isotropic, so `s = ∅`.
  have h_conj : ((Z.val.map (Φ v))ᴴ * J.val.map (Φ v) * Z.val.map (Φ v)).PosDef :=
    (Z.map (Φ v)).isUnit.posDef_star_left_conjugate_iff.mpr h_pos
  obtain rfl : s = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun i hi ↦ (h_conj.diag_pos (i := i)).ne' ?_
    simpa [mul_apply] using congrArg (Φ v) (hZ.isotropic i hi i hi)
  -- With the dual basis `Y`, `y = Y⁻¹ x` lies in `Cf` and is a frame for the form `β ∈ F`, and so
  -- is the representative `r = rep β y` of its coset.
  let Y : GL n E := formDual J Z
  let β : Matrix n n E := Y.valᴴ * J.val * Y.val
  let y : GL n (𝔸f E) := toFinGL Y⁻¹ * x
  have hβ_mem : β ∈ F := by simpa [formDualOff, projectionOff] using hZ.gram_mem
  have h_finite_part : finitePartGL (Y⁻¹.map toAdele * g) = y := by aesop
  have hy_mem : y ∈ Cf := by
    rw [← h_finite_part]
    exact hZ.finitePart_mem
  have hy : IsFrameFor β y := (IsFrameFor.conj_iff y Y).mpr (by simpa [y] using h_frame)
  obtain ⟨hr, hr_coset⟩ :
      IsFrameFor β (rep β y) ∧ (rep β y : GL n (𝔸f E) ⧸ V) = (y : GL n (𝔸f E) ⧸ V) :=
    Classical.epsilon_spec (p := fun x ↦ IsFrameFor β x ∧ (x : GL n (𝔸f E) ⧸ V) = y) ⟨y, hy, rfl⟩
  -- `x = Y y`, so `x` and `r` lie in one double coset.
  refine ⟨β, hβ_mem, y, ⟨y, hy_mem, rfl⟩, ?_⟩
  have hx : x = toFinGL Y * y := by simp [y]
  rw [hx]
  exact doubleCoset_mk_eq_of_isFrameFor hr hy hr_coset Y

end FiniteClasses

/-!
## Definite forms, their Hecke action and their trace

Conventions: `New.Variety.IsSignedFrame x 1` says that `x` is a frame for a rational form that is
positive definite at every infinite place (a definite frame).
-/

section DefiniteTrace

open Set DoubleCoset Quotient Submodule

open scoped NumberField

namespace New.Variety

variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] [DecidableEq n] (𝔑 : 𝓞 E) {W : Type}
  [AddCommGroup W] [Module ℂ W] (ξ : Representation ℂ (GL n E) W)

/-- Forms on the definite frames: the functions `φ` from `GL n` of the finite adeles to `W`
such that `φ (y x) = ξ y (φ x)` for `y` in `GL n E`; `φ x = 0` unless
`New.Variety.IsSignedFrame x 1` holds, that is, unless `x` is a frame for a totally positive
definite rational form (the submodule `pi S ⊥` asks for vanishing on `S`); and `φ (x k) = φ x`
for `k` in the principal level `levelGU n 𝔑`. -/
abbrev definiteForms : Submodule ℂ (GL n (𝔸f E) → W) :=
  -- left equivariance under `GL n E`
  ξ.coindV toFinGL ⊓
    -- vanishing at every `x` that is not a definite frame
    Submodule.pi {x : GL n (𝔸f E) | ¬IsSignedFrame x 1} ⊥ ⊓
    -- right invariance under the level
    levelSpace (rightRegular ℂ (GL n (𝔸f E)) W) (levelGU n 𝔑)

/-- The action of the Hecke algebra of level `𝔑` on definite forms by right translation. Its
elements `a` are supported on `GUPlus E n`, and their coset function is left
`levelGU n 𝔑`-invariant. -/
def definiteForms.rep : Representation ℂ (heckeAlgebra n ℂ 𝔑) (definiteForms 𝔑 ξ) :=
  Representation.subrepresentation
    ((rightRegular ℂ (GL n (𝔸f E)) W).asAlgebraHom.comp (heckeAlgebra n ℂ 𝔑).val).toMonoidHom
    (definiteForms 𝔑 ξ) fun a φ hφ ↦ by
      -- `a` is supported on `GUPlus E n` (`ha_span`) and its coset function is left
      -- `K`-invariant (`ha_fixed`).
      obtain ⟨ha_span, ha_fixed⟩ := a.prop
      obtain ⟨hφ_equivariant_support, hφ_level⟩ := hφ
      refine ⟨?_, ha_fixed hφ_level⟩
      -- Equivariance and support are preserved by each right translation by an element of `GUPlus`,
      -- hence by their linear combinations.
      refine (comap ((rightRegular ℂ (GL n (𝔸f E)) W).asAlgebraHom.toLinearMap.flip φ)
        (ξ.coindV toFinGL ⊓ Submodule.pi {x : GL n (𝔸f E) | ¬IsSignedFrame x 1} ⊥)).span_le.mpr ?_
        ha_span
      -- `↓` rewrites the image inclusion first, before the rest unfolds.
      simp_all [↓image_subset_iff, isSignedFrame_mul_iff 1, GUPlus, mul_assoc, subset_def, ratConj]

variable (n) in
/-- The definite classes: the double cosets `GL n E \ GL n (𝔸f E) / K`, with `K = levelGU n 𝔑`,
whose chosen representative is a definite frame. -/
abbrev DefiniteClass : Type :=
  {c : DoubleCosets toFinGL.range (levelGU n 𝔑) // IsSignedFrame c.out 1}

end New.Variety

namespace New.Variety

variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E} {W : Type}
  [AddCommGroup W] [Module ℂ W] (ξ : Representation ℂ (GL n E) W)

private lemma mem_GU_of_mem_levelGU {k : GL n (𝔸f E)} (hk : k ∈ levelGU n 𝔑) : k ∈ GU E n :=
  levelGU_le_GU hk

/-- At a neat level `𝔑` there are only finitely many definite classes. -/
lemma finite_definiteClass (hN : IsNeat n 𝔑) : Finite (DefiniteClass n 𝔑) := by
  -- The definite classes are among the classes of signed frames, which are finitely many.
  have h_classes_finite : (DoubleCoset.mk toFinGL.range (levelGU n 𝔑) ''
      {x : GL n (𝔸f E) | ∃ ℓ : Matrix n n ℂ, IsSignedFrame x ℓ}).Finite :=
    finite_isSignedFrame_classes (isOpen_congruenceGL_span hN.ne_zero)
  exact Set.Finite.to_subtype (h_classes_finite.subset fun c hc ↦ ⟨c.out, ⟨1, hc⟩, c.out_eq⟩)

namespace DefiniteClass

/-- The chosen representative `x_j` of the definite class `j`. -/
def frame (j : DefiniteClass n 𝔑) : GL n (𝔸f E) := j.val.out

/-- The representative of a definite class is a definite frame. -/
lemma isSignedFrame_frame (j : DefiniteClass n 𝔑) : IsSignedFrame j.frame 1 := j.property

/-- The coset `y x_j K`. -/
def coset (j : DefiniteClass n 𝔑) (y : GL n E) : GL n (𝔸f E) ⧸ levelGU n 𝔑 :=
  QuotientGroup.mk (toFinGL y * j.frame)

/-- The coset `y x_j K` is `g K` if and only if `g⁻¹ y x_j` lies in `K = levelGU n 𝔑`. -/
lemma coset_eq_mk_iff {j : DefiniteClass n 𝔑} {y : GL n E} {g : GL n (𝔸f E)} :
    j.coset y = QuotientGroup.mk g ↔ g⁻¹ * (toFinGL y * j.frame) ∈ levelGU n 𝔑 :=
  eq_comm.trans QuotientGroup.eq

/-- At a neat level the coset `y x_j K` determines the class `j` and the rational matrix `y`. -/
lemma eq_and_eq_of_coset_eq (hN : IsNeat n 𝔑) {i j : DefiniteClass n 𝔑} {y z : GL n E}
    (h_coset : i.coset y = j.coset z) : i = j ∧ y = z := by
  have h_mem : i.frame⁻¹ * toFinGL (y⁻¹ * z) * j.frame ∈ levelGU n 𝔑 := by
    simpa [mul_assoc] using QuotientGroup.eq.mp h_coset
  -- By neatness only `1` fixes the coset of a definite frame.
  have h_free (γ : GL n E) (hγ : j.frame⁻¹ * toFinGL γ * j.frame ∈ levelGU n 𝔑) : γ = 1 :=
    hN.eq_one_of_mem_levelGU j.isSignedFrame_frame hγ (by simp [ratConj])
  obtain ⟨h_class, h_one⟩ : i.val = j.val ∧ y⁻¹ * z = 1 :=
    eq_and_eq_one_of_doubleCoset_rep out_eq h_free (y⁻¹ * z) h_mem
  exact ⟨Subtype.ext h_class, inv_mul_eq_one.mp h_one⟩

/-- The definite frames are the elements of the cosets `y x_j K`. -/
lemma isSignedFrame_one_iff (g : GL n (𝔸f E)) :
    IsSignedFrame g 1 ↔
      ∃ (j : DefiniteClass n 𝔑) (y : GL n E), j.coset y = QuotientGroup.mk g := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · obtain ⟨c, y, k, rfl⟩ := exists_eq_map_mul_rep_mul toFinGL (levelGU n 𝔑) out_eq g
    -- Here `g = y x k` with `x = c.out`; moving it by `y⁻¹` and `k⁻¹` gives `x`.
    have hc : IsSignedFrame c.out 1 := by
      simpa [mul_assoc, ratConj] using hg.mul y⁻¹ (inv_mem (mem_GU_of_mem_levelGU k.prop))
    exact ⟨⟨c, hc⟩, y, (QuotientGroup.mk_mul_of_mem _ k.prop).symm⟩
  · rintro ⟨j, y, h_coset⟩
    -- `g = y x_j k⁻¹` with `k = g⁻¹ y x_j` in the level.
    have h_mem : g⁻¹ * (toFinGL y * j.frame) ∈ levelGU n 𝔑 := coset_eq_mk_iff.mp h_coset
    simpa [mul_assoc, ratConj] using
      j.isSignedFrame_frame.mul y (inv_mem (mem_GU_of_mem_levelGU h_mem))

/-- The orbit under `GL n E` of the marked triple `(x_j K, y⁻¹, μ)`. A triple is a coset of
`levelGU n 𝔑`, an element of `GL n E` and an index in `n`; `γ` sends `(x K, z, μ)` to
`(γ x K, γ z γ⁻¹, μ)`. -/
def orbit : DefiniteClass n 𝔑 × GL n E × n →
    MulAction.orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n) :=
  fun (j, y, μ) ↦ ⟦(QuotientGroup.mk j.frame, y⁻¹, μ)⟧

/-- At a neat level distinct triples `(j, y, μ)` give distinct orbits `orbit (j, y, μ)`. -/
lemma orbit_injective (hN : IsNeat n 𝔑) : (orbit (n := n) (𝔑 := 𝔑)).Injective := by
  rintro ⟨i, y, μ⟩ ⟨j, z, ν⟩ h_orbit
  -- `hγ` says `γ • (x_j K, z⁻¹, ν) = (x_i K, y⁻¹, μ)`.
  obtain ⟨γ, hγ⟩ := Quotient.exact h_orbit
  -- `γ` moves `x_j K` to `x_i K`, so `i = j` and `γ = 1`.
  have h_coset : j.coset γ = i.coset 1 := (congrArg Prod.fst hγ).trans (by simp [coset])
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_coset_eq hN h_coset
  have h_marks : (1 * z⁻¹ * 1⁻¹, ν) = (y⁻¹, μ) := congrArg Prod.snd hγ
  obtain ⟨rfl, rfl⟩ : z = y ∧ ν = μ := by simpa using h_marks
  rfl

variable (a : heckeAlgebra n ℂ 𝔑) (w : Polynomial E → n → ℂ)

/-- The definite term of the orbit of `(x_j K, y⁻¹, μ)`: the coefficient of `a` at `x_j⁻¹ y x_j K`
times the weight `w` at the characteristic polynomial of `y⁻¹` and `μ`. -/
lemma countTerm_orbit (j : DefiniteClass n 𝔑) (y : GL n E) (μ : n) :
    countTerm False a w (orbit (j, y, μ)) =
      heckeCosetFn a (j.frame⁻¹ * toFinGL y * j.frame) * w (y⁻¹).val.charpoly μ := by
  simp [orbit, countTerm_mk, eigenReflection, j.isSignedFrame_frame, mul_assoc]

/-- An orbit with a nonzero definite term is the orbit of some `(x_j K, y⁻¹, μ)`. -/
lemma support_countTerm_subset_range_orbit : (countTerm False a w).support ⊆ range orbit := by
  rintro ⟨⟨x⟩, y, μ⟩ (h_ne : countTerm False a w ⟦(QuotientGroup.mk x, y, μ)⟧ ≠ 0)
  have hx : IsSignedFrame x 1 := by
    by_contra hx
    simp [countTerm_mk, eigenReflection, hx] at h_ne
  -- If `x K = γ x_j K`, then `γ⁻¹` moves the triple to one with first entry `x_j K`.
  obtain ⟨j, γ, h_coset⟩ := (isSignedFrame_one_iff (𝔑 := 𝔑) x).mp hx
  have h_mem : (toFinGL γ⁻¹ * x)⁻¹ * j.frame ∈ levelGU n 𝔑 := by
    simpa [mul_assoc] using coset_eq_mk_iff.mp h_coset
  exact ⟨(j, (γ⁻¹ * y * γ)⁻¹, μ), sound ⟨γ⁻¹, Prod.ext (QuotientGroup.eq.mpr h_mem) rfl⟩⟩

end DefiniteClass

open DefiniteClass

/-- At a neat level only finitely many orbits of triples have a nonzero definite term
`countTerm False a w` (the flag `False` selects the orbits whose frame is definite). -/
lemma finite_support_countTerm_definite (hN : IsNeat n 𝔑) (a : heckeAlgebra n ℂ 𝔑)
    (w : Polynomial E → n → ℂ) : (countTerm False a w).support.Finite := by
  have h_finite_classes : Finite (DefiniteClass n 𝔑) := finite_definiteClass hN
  -- For each `j` the cosets `x_j⁻¹ y x_j K` are distinct, so only finitely many of them lie in the
  -- finite support of `heckeCosetFn a`.
  have h_fibre (j : DefiniteClass n 𝔑) :
      {y : GL n E | heckeCosetFn a (j.frame⁻¹ * toFinGL y * j.frame) ≠ 0}.Finite := by
    refine (heckeCosetFn a).hasFiniteSupport.preimage fun y _ z _ hyz ↦ ?_
    have h_coset : j.coset y = j.coset z :=
      QuotientGroup.eq.mpr (by simpa [mul_assoc] using QuotientGroup.eq.mp hyz)
    exact (eq_and_eq_of_coset_eq hN h_coset).right
  have h_triples : (orbit ⁻¹' (countTerm False a w).support).Finite := by
    refine (finite_iUnion fun j ↦ ((h_fibre j).prod finite_univ).image (Prod.mk j)).subset ?_
    rintro ⟨j, y, μ⟩ h_ne
    rw [mem_preimage, Function.mem_support, countTerm_orbit] at h_ne
    exact mem_iUnion.mpr ⟨j, (y, μ), ⟨left_ne_zero_of_mul h_ne, mem_univ μ⟩, rfl⟩
  exact finite_of_finite_preimage h_triples (support_countTerm_subset_range_orbit a w)

variable [Module.Finite ℂ W]

/-- Let `ξ` be a representation of `GL_n(E)` on a finite-dimensional complex space `W`, and let the
level `𝔑` be neat (`hN`). The definite forms are the functions `φ : GL_n(𝔸f E) → W` with
`φ(yx) = ξ(y) φ(x)` for `y ∈ GL_n(E)`, which vanish off definite frames and are right-invariant
under `K = levelGU n 𝔑`. This space is finite-dimensional, and the trace on it of a Hecke element
`a` acting by right translation equals `∑_j ∑_{y ∈ GL_n(E)} f_a(x_j⁻¹ y x_j) · tr ξ(y)`. In this sum
`j` runs over the definite classes in `GL_n(E) \ GL_n(𝔸f E) / K` with chosen representatives
`x_j = j.frame`, and `f_a = heckeCosetFn a` is the function `∑ a_g 1_{gK}` for `a = ∑ a_g [g]`. -/
lemma finite_definiteForms_and_trace_eq_finsum_definiteClass (hN : IsNeat n 𝔑)
    (a : heckeAlgebra n ℂ 𝔑) :
    Module.Finite ℂ (definiteForms 𝔑 ξ) ∧
    (definiteForms.rep 𝔑 ξ a).trace ℂ (definiteForms 𝔑 ξ) =
      ∑ᶠ (j : DefiniteClass n 𝔑) (y : GL n E),
        heckeCosetFn a (j.frame⁻¹ * toFinGL y * j.frame) * (ξ y).trace ℂ W := by
  classical
  -- This is `trace_eq_weighted_sum` with all weights equal to `1`: a definite frame `g` lies in
  -- exactly one coset `y x_j K`, and any other `g` lies in none.
  have h_finite_classes : Finite (DefiniteClass n 𝔑) := finite_definiteClass hN
  have h_fintype_classes : Fintype (DefiniteClass n 𝔑) := .ofFinite _
  have h_finite (j : DefiniteClass n 𝔑) (g : GL n (𝔸f E)) :
      {y : GL n E | j.coset y = QuotientGroup.mk g}.Finite :=
    Set.Subsingleton.finite fun y hy z hz ↦ (eq_and_eq_of_coset_eq hN (hy.trans hz.symm)).right
  let S (j : DefiniteClass n 𝔑) (g : GL n (𝔸f E)) : Finset (GL n E) := (h_finite j g).toFinset
  have h_mem_S (j : DefiniteClass n 𝔑) (g : GL n (𝔸f E)) (y : GL n E) :
      y ∈ S j g ↔ g⁻¹ * (toFinGL y * j.frame) ∈ levelGU n 𝔑 := by
    simp [S, coset_eq_mk_iff]
  have h_S_eq_empty (g : GL n (𝔸f E)) (hg : ¬IsSignedFrame g 1) (j : DefiniteClass n 𝔑) :
      S j g = ∅ := by
    ext y
    simpa [S] using fun h_coset ↦ hg ((isSignedFrame_one_iff g).mpr ⟨j, y, h_coset⟩)
  have h_count (g : GL n (𝔸f E)) (hg : IsSignedFrame g 1) :
      ∑ j : DefiniteClass n 𝔑, (1 : ℂ) * (S j g).card = 1 := by
    obtain ⟨i, y, h_coset⟩ := (isSignedFrame_one_iff (𝔑 := 𝔑) g).mp hg
    have h_mem (j : DefiniteClass n 𝔑) (z : GL n E) : z ∈ S j g ↔ j = i ∧ z = y := by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred, ← h_coset]
      exact ⟨eq_and_eq_of_coset_eq hN, fun ⟨hj, hz⟩ ↦ by rw [hj, hz]⟩
    have h_S (j : DefiniteClass n 𝔑) : S j g = if j = i then {y} else ∅ := by
      ext z
      by_cases hj : j = i <;> simp [h_mem, hj]
    simp [h_S, apply_ite Finset.card]
  -- The representatives are the frames `x_j`; the twists `σ` and `s` are identities.
  let σ : GL n (𝔸f E) ≃* GL n (𝔸f E) := 1
  have h_weighted : Module.Finite ℂ (definiteForms 𝔑 ξ) ∧
      (definiteForms.rep 𝔑 ξ a).trace ℂ (definiteForms 𝔑 ξ) =
        ∑ j : DefiniteClass n 𝔑, 1 * ∑ᶠ y : GL n E, cosetFn (levelGU n 𝔑) a.val
          (j.frame⁻¹ * σ (toFinGL y) * σ j.frame) * (1 * ξ y).trace ℂ W :=
    trace_eq_weighted_sum (definiteForms 𝔑 ξ).subtype (subtype_injective _) (range_subtype _)
      frame (fun _ ↦ 1) S h_mem_S h_S_eq_empty (fun g hg ↦ h_count g (not_not.mp hg)) σ rfl
      fun _ ↦ rfl
  rw [finsum_eq_sum_of_fintype]
  simpa [σ] using h_weighted

/-- At a neat level the space of definite forms with values in `ξ` is finite-dimensional. -/
lemma finite_definiteForms (hN : IsNeat n 𝔑) : Module.Finite ℂ (definiteForms 𝔑 ξ) :=
  (finite_definiteForms_and_trace_eq_finsum_definiteClass ξ hN 1).left

/-- At a neat level the trace of a Hecke element `a` on the definite forms is the sum, over the
definite classes `j` and the rational matrices `y`, of `heckeCosetFn a` (the function `∑ a_g [gK]`
of `a` on cosets) at `x_j⁻¹ y x_j`, where `x_j = j.frame` is the frame of `j`, times `tr (ξ y)`. -/
lemma trace_definiteForms_eq_finsum_definiteClass (hN : IsNeat n 𝔑) (a : heckeAlgebra n ℂ 𝔑) :
    (definiteForms.rep 𝔑 ξ a).trace ℂ (definiteForms 𝔑 ξ) =
      ∑ᶠ (j : DefiniteClass n 𝔑) (y : GL n E),
        heckeCosetFn a (j.frame⁻¹ * toFinGL y * j.frame) * (ξ y).trace ℂ W :=
  (finite_definiteForms_and_trace_eq_finsum_definiteClass ξ hN a).right

/-- The trace formula on the definite side. Let `W` be finite-dimensional, `𝔑` neat and `a` a
regular Hecke element. Suppose `tr ξ(y⁻¹) = ∑ i, w P i` whenever the characteristic polynomial `P`
of `y` is separable. Then the trace of `a` on definite forms is the sum, over all orbits of triples,
of the definite terms `countTerm False a w` (the flag `False` selects definite frames). On the orbit
of `(x_j K, y⁻¹, μ)` this term is `heckeCosetFn a (x_j⁻¹ y x_j) * w (y⁻¹).charpoly μ`
(`countTerm_orbit`). -/
lemma trace_definiteForms_eq_finsum_countTerm (hN : IsNeat n 𝔑) {a : heckeAlgebra n ℂ 𝔑}
    {w : Polynomial E → n → ℂ} (ha : IsRegularHecke a)
    (hw : ∀ y : GL n E, y.val.charpoly.Separable →
      (ξ y⁻¹).trace ℂ W = ∑ i : n, w y.val.charpoly i) :
    (definiteForms.rep 𝔑 ξ a).trace ℂ (definiteForms 𝔑 ξ) =
      ∑ᶠ c : MulAction.orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n),
        countTerm False a w c := by
  -- Only the orbits of the triples `(x_j K, y⁻¹, μ)` count, and these orbits are distinct.
  have h_orbits : ∑ᶠ c, countTerm False a w c =
      ∑ᶠ (j : DefiniteClass n 𝔑) (y : GL n E) (μ : n), countTerm False a w (orbit (j, y, μ)) := by
    rw [← finsum_curry₃ (fun p ↦ countTerm False a w (orbit p))
        ((finite_support_countTerm_definite hN a w).preimage (orbit_injective hN).injOn),
      ← finsum_mem_range (orbit_injective hN), finsum_mem_def,
      indicator_eq_self.mpr (support_countTerm_subset_range_orbit a w)]
  -- Either the coefficient of `a` vanishes, or `y` is regular and `hw` applies.
  have h_term (j : DefiniteClass n 𝔑) (y : GL n E) :
      heckeCosetFn a (j.frame⁻¹ * toFinGL y * j.frame) * (ξ y).trace ℂ W =
        ∑ᶠ μ : n, countTerm False a w (orbit (j, y, μ)) := by
    simp_rw [finsum_eq_sum_of_fintype, countTerm_orbit, ← Finset.mul_sum]
    by_cases h_coeff : heckeCosetFn a (j.frame⁻¹ * toFinGL y * j.frame) = 0
    · rw [h_coeff, zero_mul, zero_mul]
    · have h_separable : (y⁻¹).val.charpoly.Separable :=
        ha (x := j.frame) (by simpa only [invAutInFrame, inv_inv] using h_coeff)
      rw [← hw y⁻¹ h_separable, inv_inv]
  rw [trace_definiteForms_eq_finsum_definiteClass ξ hN a, h_orbits]
  simp_rw [h_term]

end New.Variety

end DefiniteTrace

end
