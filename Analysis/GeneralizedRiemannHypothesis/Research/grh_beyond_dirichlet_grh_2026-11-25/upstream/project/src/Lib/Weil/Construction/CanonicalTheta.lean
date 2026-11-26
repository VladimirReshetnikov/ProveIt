import Lib.Adelic.Landherr
import Lib.Weil.MixedModel.ThetaInvariance

/-!
# Independence of the theta functional of the chosen group element; transport and sums

The theta functional `New.Space.θ` of a space `V` is defined by transporting a theta functional of
the standard space `New.signedSpace E s` along a chosen group element. Such a functional exists by
`New.exists_isThetaFunctional_signedSpace`.

* `New.CoordChange.exists_theta_omega_map`: a vacuum-preserving change of coordinates
  (`New.CoordChange`) that respects rational vectors transports theta functionals, up to a factor of
  modulus one.
* `New.Space.exists_mapsTo_ratVectors`: a group element that matches the rational vectors of two
  spaces exists, by Landherr's theorem.
* `New.Space.theta_omega_eq_of_mapsTo_ratVectors`: `θ` does not depend on the chosen element, since
  two choices differ by a rational point.
* `New.Space.theta_omega_rho_vacElem_eq_prod_lineTheta`: with any element that matches the rational
  vectors, `θ ∘ ω(g)` of the translates of the vacuum is a product of the rank one theta functions
  `New.lineTheta`.
* `New.Space.theta_move`: moving the point of `V` by `γ` changes `θ` to `θ ∘ ω(γ)`.
* `New.Space.theta_boxProd`: `θ` is multiplicative on orthogonal sums.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.signedSpace`: the standard space with matrix diag(s), a sum of lines.
* `New.Space.IsThetaFunctional`: A theta functional of V: a bounded θ on
  `Model (adelicHeisenberg E s)`, invariant under the rational Heisenberg operators, with
  |θ(ρ(x)vac)|² of mean 1 over 𝔸^n modulo rational points.
* `New.Space.boxProd`: For a splitting of the coordinates, the product 𝒮(V₁) × 𝒮(V₂) → 𝒮(V).

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

namespace New.Space

open Function Matrix G

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n₁ n₂ : Type*} [Fintype n] [DecidableEq n]
  [Fintype n₁] [DecidableEq n₁] [Fintype n₂] {s : n → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ}
  {σ : ℂ →+* ℂ} [RingHomIsometric σ] (D : CoordChange E σ s₁ s) {W V : Space E n s}
  (V₁ : Space E n₁ s₁)

/-- Let `σ` be an isometric ring endomorphism of ℂ that is an involution. Let `D` be a change of
adelic coordinates `D.φ` from 𝔸^n to 𝔸^{n₁} that keeps the Heisenberg bicharacter up to `σ`, with
induced map `D.map : 𝒮 V₁ → 𝒮 V`, and let `g : G E s` be such that `g • x` is a rational vector of
`V` whenever `D.φ x` is a rational vector of `V₁`. Then there is `c : ℂ` with `‖c‖ = 1` such that
`V₁.θ f = c * σ (V.θ (V.ω g (D.map f)))` for all `f : 𝒮 V₁`. -/
lemma _root_.New.CoordChange.exists_theta_omega_map [RingHomInvPair σ σ] (V : Space E n s)
    (g : G E s) (hΓ : ∀ x : n → 𝔸 E, D.φ x ∈ V₁.ratVectors → g • x ∈ V.ratVectors) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : 𝒮 V₁, V₁.θ f = c * σ (V.θ (V.ω g (D.map f))) := by
  -- f ↦ ω(g) (D.map f) intertwines the Heisenberg operators along g φ⁻¹ and keeps the norm of the
  -- vacuum, so f ↦ σ θ_V(ω(g) (D.map f)) is a theta functional of V₁ (`IsThetaFunctional.comp`).
  have h_heis (x : n₁ → 𝔸 E) (f : 𝒮 V₁) :
      V.ω g (D.map (V₁.ϱ x f)) = V.ϱ (g.adeleMatrix *ᵥ D.φ.symm x) (V.ω g (D.map f)) := by
    rw [← omega_rho, ← D.map_rho, D.φ.apply_symm_apply]
  have h_norm : V.dataInner (V.ω g (D.map V₁.vacElem)) (V.ω g (D.map V₁.vacElem)) = 1 := by
    rw [D.map_vacElem, dataInner_omega, dataInner_vacElem_vacElem]
  have h_rat (x : n₁ → 𝔸 E) (hx : x ∈ V₁.ratVectors) : g • D.φ.symm x ∈ V.ratVectors :=
    hΓ (D.φ.symm x) (by rwa [D.φ.apply_symm_apply])
  -- the functional `f ↦ σ (θ_V (ω(g) (D.map f)))`
  let F : Heisenberg.IsVacuum.Model (adelicHeisenberg E s₁) →L[ℂ] ℂ :=
    σ.toSemilinearMap.mkContinuous 1 (by simp) ∘SL V.rawTheta ∘SL (V.ω g ∘SL D.map (V₁ := V₁))
  have : ContinuousConstSMul (G E s) (n → 𝔸 E) := ContinuousSMul.continuousConstSMul
  obtain ⟨h_inv, h_mean⟩ : V₁.IsThetaFunctional F :=
    V.isThetaFunctional_rawTheta.comp V (V.ω g ∘SL D.map (V₁ := V₁))
      (D.φ.symm.trans (.mk' (.smul g) (mulVec_add _))) h_rat h_heis h_norm
  -- Invariant functionals are proportional, so θ_{V₁} is a multiple of it; both have mean 1,
  -- which gives c c̄ = 1.
  obtain ⟨h_inv₁, h_mean₁⟩ := V₁.isThetaFunctional_rawTheta
  obtain ⟨c, hc⟩ := IsThetaFunctional.eq_smul ⟨h_inv, h_mean⟩ h_inv₁
  have h_sq : c * starRingEnd ℂ c = 1 := by
    -- each term of the mean of `θ_{V₁}` is `c c̄` times the term of the mean of `F`
    simpa only [hc, _root_.smul_apply, smul_eq_mul, map_mul, mul_mul_mul_comm c,
      quotMean_const_mul, h_mean, mul_one] using h_mean₁
  have h_sq_real : ‖c‖ ^ 2 = 1 := by exact_mod_cast (Complex.mul_conj' c).symm.trans h_sq
  simp only [theta_eq_rawTheta]
  exact ⟨c, (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).mp h_sq_real,
    fun f ↦ DFunLike.congr_fun hc f⟩

/-- Let `V` and `W` be two hermitian spaces with a point (a matrix `J` over `E` and a point `x` in
`GL_n(𝔸)`) over the CM number field `E` with Weil data, and suppose they have the same signs `s`.
Then some `g` in the adelic unitary group `G E s` carries the rational points of `V` (the vectors
`x_V⁻¹ y`, `y ∈ E^n`) into those of `W`. -/
lemma exists_mapsTo_ratVectors : ∃ g : G E s, ∀ γ ∈ V.ratVectors, g • γ ∈ W.ratVectors := by
  -- By Landherr's theorem `V.x = a⁻¹ * W.x * g` with `a` rational, so `g` sends the rational point
  -- `y` of `V` to the rational point `a *ᵥ y` of `W`.
  obtain ⟨a, g, -, hx, -⟩ := W.exists_x_eq_and_ratEmbed_conj_eq V
  refine ⟨g, ?_⟩
  rintro γ ⟨y, rfl⟩
  exact ⟨a *ᵥ y, by simp [hx, adeleMatrix, RingHom.map_mulVec, vecAtPoint, comp_def]⟩

/-- Entry `j` of `M *ᵥ (column i of N)` is the entry `(j, i)` of `M * N`. -/
private lemma _root_.Matrix.mulVec_col_apply_eq_mul_apply {R m n o : Type*} [Fintype n]
    [NonUnitalNonAssocSemiring R] (M : Matrix m n R) (N : Matrix n o R) (i : o) (j : m) :
    (M *ᵥ N.col i) j = (M * N) j i :=
  rfl

/-- The functional `θ_V` does not depend on the group element chosen in its definition: for every
`g` in the adelic unitary group `G E s` that carries the rational vectors of the sum of lines with
signs `s` into the rational vectors of `V`, the functional `θ_V ∘ ω(g)` is the fixed theta
functional of the sum of lines. -/
lemma theta_omega_eq_of_mapsTo_ratVectors {g : G E s}
    (h_maps : ∀ γ ∈ (signedSpace E s).ratVectors, g • γ ∈ V.ratVectors) (f : 𝒮 V) :
    V.θ (V.ω g f) = (exists_isThetaFunctional_signedSpace (E := E) (s := s)).choose f := by
  -- By definition θ_V is the fixed functional after ω(g₀), for a chosen g₀ that carries the
  -- rational vectors of V to those of the sum of lines. Then g g₀ keeps the rational vectors
  -- of V, so it is a rational point γ; ω(γ⁻¹) fixes θ_V, and g₀ γ⁻¹ g = 1.
  have h_exists :
      ∃ g₀ : G E s, ∀ γ ∈ V.ratVectors, G.adeleMatrix g₀ *ᵥ γ ∈ (signedSpace E s).ratVectors :=
    exists_mapsTo_ratVectors
  let g₀ : G E s := h_exists.choose
  have h_def (f' : 𝒮 V) : V.θ f' = exists_isThetaFunctional_signedSpace.choose (V.ω g₀ f') := by
    -- `erw`, `rfl`: `rawTheta` is stated on `Model (adelicHeisenberg E s)`, which `𝒮 V` unfolds to,
    -- so plain `rw` and `simp` find no type-correct motive for `dite_eq_left`
    erw [theta_eq_rawTheta, rawTheta, dite_eq_left h_exists]
    rfl
  -- These vectors are the columns of `V.x * (g * g₀).adeleMatrix * V.x⁻¹`.
  have h_rat (i : n) :
      V.x *ᵥ g.adeleMatrix *ᵥ g₀.adeleMatrix *ᵥ V.vecAtPoint (Pi.single i 1) ∈ New.ratVectors E n :=
    V.mem_ratVectors_iff.mp (h_maps _ (h_exists.choose_spec _ ⟨Pi.single i 1, rfl⟩))
  have h_entry : ∀ j i : n, (V.x * (g * g₀).adeleMatrix * V.x⁻¹) i j ∈ toAdele.range := by
    simpa [Pi.apply_single fun _ ↦ toAdele (E := E), vecAtPoint, comp_def, mem_ratVectors,
      Matrix.mulVec_mulVec, ratAdeles, Matrix.mulVec_col_apply_eq_mul_apply] using h_rat
  obtain ⟨γ, hγ⟩ : g * g₀ ∈ V.Γ := V.mem_Gamma_iff_range.mpr fun i j ↦ h_entry j i
  rw [← theta_omega_ratEmbed γ⁻¹, h_def, rep_apply_apply, rep_apply_apply]
  simp [hγ]

/-- The law that fixes the phase of `θ`: for every `g` that carries the rational vectors of the
sum of lines into those of `V`, the value of `θ_V ∘ ω(g)` on the translate of the vacuum by `x`
is the product of the rank-one theta values at the coordinates of `x`. -/
lemma theta_omega_rho_vacElem_eq_prod_lineTheta {g : G E s}
    (h_maps : ∀ γ ∈ (signedSpace E s).ratVectors, g • γ ∈ V.ratVectors) (x : n → 𝔸 E) :
    V.θ (V.ω g (V.ϱ x V.vacElem)) = ∏ i : n, lineTheta (s i) (x i) := by
  rw [theta_omega_eq_of_mapsTo_ratVectors h_maps]
  exact (exists_isThetaFunctional_signedSpace (E := E) (s := s)).choose_spec.2 x

/-- Let `W` and `V` be hermitian spaces with a point over the CM number field `E` with Weil data.
Both have the same signs `s`, and `g` is an element of the adelic unitary group `G E s`. If `g`
carries the rational points of `W` (the vectors `x_W⁻¹ y`, `y ∈ E^n`) into those of `V`, then for
every `f` in the Banach space `𝒮 V` the theta functionals satisfy `W.θ f = V.θ (V.ω g f)`, that is,
`θ_W = θ_V ∘ ω(g)` with `ω` the Weil representation. The statement makes sense because `𝒮` and `ω`
depend only on the signs. -/
lemma theta_eq_theta_omega {W V : Space E n s} {g : G E s}
    (h_rat : ∀ y ∈ W.ratVectors, g • y ∈ V.ratVectors) (f : 𝒮 V) : W.θ f = V.θ (V.ω g f) := by
  -- Let `p` carry the sum of lines to `W`; then `g p` carries it to `V`, and both sides are the
  -- theta functional of the sum of lines at `ω(p⁻¹) f`.
  obtain ⟨p, hp⟩ : ∃ p : G E s, ∀ y ∈ (signedSpace E s).ratVectors, p • y ∈ W.ratVectors :=
    exists_mapsTo_ratVectors
  have hgp (y : n → 𝔸 E) (hy : y ∈ (signedSpace E s).ratVectors) :
      (g * p) • y ∈ V.ratVectors := by
    simpa only [mul_smul] using h_rat _ (hp y hy)
  have h_eq : W.θ (V.ω p (V.ω p⁻¹ f)) = V.θ (V.ω (g * p) (V.ω p⁻¹ f)) :=
    (theta_omega_eq_of_mapsTo_ratVectors hp _).trans
      (theta_omega_eq_of_mapsTo_ratVectors hgp _).symm
  rwa [rep_apply_apply, rep_apply_apply, mul_inv_cancel, mul_inv_cancel_right, map_one,
    one_apply_eq_self] at h_eq

/-- Let `V = (J, x)` be a hermitian space with a point over the CM number field `E` with Weil data,
and let `γ` be in the adelic unitary group `G E s`. The space `V.move γ = (J, xγ)` has the same
matrix as `V` and its point moved by `γ`. Its theta functional is `θ_V ∘ ω(γ)`, that is,
`(V.move γ).θ f = V.θ (V.ω γ f)` for every `f` in the Banach space `𝒮 V`, where `ω` is the Weil
representation. -/
lemma theta_move (V : Space E n s) (γ : G E s) (f : 𝒮 V) :
    (V.move γ).θ f = V.θ (V.ω γ f) := by
  refine theta_eq_theta_omega (fun _ ⟨y, hy⟩ ↦ ⟨y, ?_⟩) f
  simp [← hy, move, G.adeleMatrix, vecAtPoint]

/-- If `V` has the rational points of the sum of lines (`V.vecAtPoint y`, the vector `x_V⁻¹ y`,
equals that of the sum of lines for every `y ∈ E^n`), the theta function of its vacuum,
`x ↦ V.vacElem x`, which is `θ_V` at the translate `ϱ(x)` of the vacuum, is the product of the
rank-one theta values at the coordinates. -/
lemma vacElem_apply_eq_prod_lineTheta
    (h : ∀ y : n → E, V.vecAtPoint y = (signedSpace E s).vecAtPoint y) (x : n → 𝔸 E) :
    V.vacElem x = ∏ i : n, lineTheta (s i) (x i) := by
  have h_one : ∀ γ ∈ (signedSpace E s).ratVectors, (1 : G E s) • γ ∈ V.ratVectors := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, (h y).trans (one_smul (G E s) _).symm⟩
  simpa using V.theta_omega_rho_vacElem_eq_prod_lineTheta h_one x

/-- The functional `θ` is multiplicative: if the point of `V` is the block sum of the points of
`V₁` and `V₂` along `e`, then `θ_V (f₁ ⊠ f₂) = θ_{V₁} f₁ * θ_{V₂} f₂`. -/
lemma theta_boxProd [DecidableEq n₂] {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂) {V₁ : Space E n₁ s₁}
    {V₂ : Space E n₂ s₂} (h_blocks : V.x.val.submatrix e e = fromBlocks V₁.x 0 0 V₂.x)
    (f₁ : 𝒮 V₁) (f₂ : 𝒮 V₂) : V.θ (V.boxProd hs f₁ f₂) = V₁.θ f₁ * V₂.θ f₂ := by
  -- Move the standard spaces to V₁, V₂ by g₁, g₂; the block matrix does the same for V.
  obtain ⟨g₁, hg₁⟩ := exists_mapsTo_ratVectors (V := signedSpace E s₁) (W := V₁)
  obtain ⟨g₂, hg₂⟩ := exists_mapsTo_ratVectors (V := signedSpace E s₂) (W := V₂)
  have h_sign : ∀ i : n₁ ⊕ n₂, s (e i) = (s₁ ⊕ᵥ s₂) i := congrFun hs
  have h_blk : ∀ γ ∈ (signedSpace E s).ratVectors, blockEmb hs (g₁, g₂) • γ ∈ V.ratVectors := by
    -- Each half of `γ` is rational for its sum of lines, so `gᵢ` moves it to a rational vector
    -- of `Vᵢ`; the point of `V` acts block by block.
    intro γ hγ
    have h_coord (i : n₁ ⊕ n₂) : ((signedSpace E s).x.val *ᵥ γ) (e i) ∈ ratAdeles E :=
      mem_ratVectors.mp ((signedSpace E s).mem_ratVectors_iff.mp hγ) (e i)
    have h_left : g₁ • (γ ∘ e ∘ .inl) ∈ V₁.ratVectors :=
      hg₁ _ ((signedSpace E s₁).mem_ratVectors_iff.mpr (mem_ratVectors.mpr fun i ↦ by
        simpa [signedSpace, h_sign, mulVec_diagonal] using h_coord (.inl i)))
    have h_right : g₂ • (γ ∘ e ∘ .inr) ∈ V₂.ratVectors :=
      hg₂ _ ((signedSpace E s₂).mem_ratVectors_iff.mpr (mem_ratVectors.mpr fun i ↦ by
        simpa [signedSpace, h_sign, mulVec_diagonal] using h_coord (.inr i)))
    have h_apply : ∀ i j, V.x.val (e i) (e j) = fromBlocks V₁.x.val 0 0 V₂.x.val i j :=
      congr_fun₂ h_blocks
    simpa [mem_ratVectors_iff, reindex_equiv e, h_apply, Matrix.mul_apply, mulVec, dotProduct,
      blockEmb, mem_ratVectors] using And.intro h_left h_right
  have h_mat : (blockEmb hs (g₁, g₂)).adeleMatrix.submatrix e e =
      fromBlocks g₁.adeleMatrix 0 0 g₂.adeleMatrix := by simp [blockEmb]
  -- Both sides are bounded bilinear forms, so it is enough to compare them on the vectors
  -- ω(gᵢ) ϱ(yᵢ) vac, where each side is a product over the coordinates.
  have h_vac (y₁ : n₁ → 𝔸 E) (y₂ : n₂ → 𝔸 E) :
      V.θ (V.boxProd hs (V₁.ω g₁ (V₁.ϱ y₁ V₁.vacElem)) (V₂.ω g₂ (V₂.ϱ y₂ V₂.vacElem))) =
        V₁.θ (V₁.ω g₁ (V₁.ϱ y₁ V₁.vacElem)) * V₂.θ (V₂.ω g₂ (V₂.ϱ y₂ V₂.vacElem)) := by
    rw [theta_omega_rho_vacElem_eq_prod_lineTheta hg₁,
      theta_omega_rho_vacElem_eq_prod_lineTheta hg₂,
      ← omega_boxProd hs h_mat, boxProd_rho, boxProd_vacElem,
        theta_omega_rho_vacElem_eq_prod_lineTheta h_blk]
    simp [← e.prod_comp, h_sign]
  have h_forms : .postcomp (𝒮 V₂) V.θ ∘L V.boxProd hs = .smulRight V₁.θ V₂.θ :=
    V₁.ext_of_vacElem g₁ fun y₁ ↦ V₂.ext_of_vacElem g₂ (h_vac y₁)
  simpa using DFunLike.congr_fun (DFunLike.congr_fun h_forms f₁) f₂

end New.Space
