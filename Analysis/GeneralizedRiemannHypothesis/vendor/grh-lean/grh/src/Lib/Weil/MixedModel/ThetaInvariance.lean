import Lib.Weil.MixedModel.ZeroTerm

/-!
# Mixed model of the Weil representation: Levi intertwining and invariance of θ

This file proves that the slice map x ↦ f[x] = `D.slice x f` of a splitting `D` is continuous and
integrable on `𝔸^p`. Take `g` with `g k = k a`, `a ∈ GL_p(𝔸)`, acting as `g₀` on `V₀`. Then ev
ω(g) = χ_𝔸(det a)⁻¹ ω(g₀) ev, where ev is the zero term and χ_𝔸 = `New.chiAdelic`. The file then
proves that θ is invariant under the rational unitary group. When `V₀` is zero, the function
x ↦ f[x] plays the part of a vector of the Schrödinger model on `𝔸^p`; this identification is not
stated here, and the space L²(𝔸^p) is not used.

## Main definitions and results

* `New.Space.Splitting.zeroTerm_omega_levi`: on the Levi subgroup, ev ω(g) = χ_𝔸(det a)⁻¹ ω(g₀) ev.
  The modulus of the scalar comes from `New.Space.Splitting.integral_dataInner_slice`. Its phase
  comes from `New.Space.Splitting.exists_hyperbolic_levi_multiplier_nonneg`.
* `New.Space.theta_omega_ratEmbed`: θ is invariant under the rational unitary group, acting through
  `New.Space.ratEmbed` and `New.Space.ω`. On a split space two opposite parabolic subgroups fix θ
  and generate the group (`New.Space.theta_omega_ratEmbed_of_splitting`). The general case follows
  by doubling: `V ⊕ V⁻` is split, and `γ` acts on it as `(γ, 1)`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Space.Splitting`: A decomposition V = (lE^p ⊕ kE^p) ⊥ ιV₀ over E: isotropic frames l, k with
  l*Jk = 1, an isometry ι from V₀ orthogonal to both, and rk V = rk V₀ + 2p.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.
* `New.Space.Splitting.zeroTerm`, `New.Space.Splitting.slice` (in `Lib.Weil.MixedModel.ZeroTerm`):
  the zero term ev : 𝒮 V → 𝒮 V₀, the integral of `f (ι y + k b)` over `b ∈ 𝔸^p`, and the slice
  f[x] = ev(ϱ(l x) f).

## Relation to the literature

Known result: Schrödinger and mixed models of the Weil representation and the action of parabolic
subgroups. Here the groups are adelic unitary groups of spaces `New.Space` over a CM field with
`New.WeilData`, and the vectors have integrable coefficients instead of being Schwartz functions.
The representation is normalised by its vacuum coefficient, so the formulas for the parabolic
subgroup are proved rather than taken as the definition. Source: C. Mœglin, M.-F. Vignéras, J.-L.
Waldspurger, Correspondances de Howe sur un corps p-adique, LNM 1291, 1987; S. Kudla, Splitting
metaplectic covers of dual reductive pairs, Israel J. Math. 87 (1994) 361–401; A. Weil, Acta Math.
111 (1964) n° 16–19, 41.

Known result: Adelic Weil representation of a unitary group and the invariant theta functional. Here
the CM fields have enough roots of unity and carry a splitting character and a self-dual rank-one
lattice, and the Weil representation is built without a polarisation. Vectors are integrable
coefficients against a vacuum, the splitting is fixed by the vacuum coefficient, and the sign of the
finite cocycle comes from a congruence modulo 4. Source: A. Weil, Sur certains groupes d'opérateurs
unitaires, Acta Math. 111 (1964), n° 16-19 Thm 4, n° 41 Thm 6; S. Kudla, Splitting metaplectic
covers of dual reductive pairs, Israel J. Math. 87 (1994) 361-401; H. Reiter, Metaplectic Groups and
Segal Algebras, LNM 1382 (1989) (space of data, after H. Feichtinger, On a new Segal algebra,
Monatsh. Math. 92 (1981)); E. Zelenov, p-adic Heisenberg group and Maslov index, Comm. Math. Phys.
155 (1993) 489-502, Prop. 4 (cocycle of three lattices); Robinson and Rawnsley, Mem. AMS 410 (1989)
(real normalisation).
-/

noncomputable section

namespace New.Space.Splitting

/-!
## Continuity and integrability of x ↦ f[x]

Integrability follows from the bound `New.Space.Splitting.tsum_enorm_slice_le` on sums over
`E^p` and from compactness of `𝔸^p / E^p`.
-/

section MixedModelIntegrable

open MeasureTheory Equiv

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {n₀ p : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p)

/-- For a Witt decomposition `D` of `V` as `(l E^p ⊕ k E^p) ⊥ ι V₀` over a CM field `E` with Weil
data, and any `f` in 𝒮(V), the slice `x ↦ D.slice x f` is a continuous map from 𝔸^p to 𝒮(V₀) with
its own topology. Here `D.slice x f` is the mixed-model value, namely the zero term along `k` of
`ϱ(l x) f`. -/
@[fun_prop]
lemma continuous_slice (f : 𝒮 V) : Continuous fun x : p → 𝔸 E ↦ D.slice x f := by
  change Continuous fun x : p → 𝔸 E ↦ D.zeroTerm (V.ϱ (D.lAdelic.mulVec x) f)
  fun_prop

/-- For a splitting of V over V₀ with p hyperbolic planes and f in 𝒮(V), the 𝒮(V₀)-valued
function x ↦ f[x] of the mixed model is integrable on 𝔸^p. -/
@[fun_prop]
lemma integrable_slice (f : 𝒮 V) : Integrable fun x : p → 𝔸 E ↦ D.slice x f := by
  -- The integral of the norm over `𝔸^p` is the integral over the quotient `𝔸^p / E^p`, which has
  -- finite measure, of sums over `E^p`; these sums are bounded.
  obtain ⟨C, hC⟩ := D.tsum_enorm_slice_le
  -- Translation by `x` is the action of `ϱ` at `D.lAdelic *ᵥ x`, which keeps the norm of `f`.
  have h_bound (x : p → 𝔸 E) : ∑' ξ : p → E, ‖D.slice (toAdele ∘ ξ + x) f‖ₑ ≤ C * ‖f‖ₑ := by
    simpa [← ofReal_norm, Heisenberg.Rep.norm_map] using! hC (V.ϱ (D.lAdelic.mulVec x) f)
  refine ⟨by fun_prop, ?_⟩
  -- Unfold the integral into an integral over the quotient of sums over the lattice `E^p`.
  calc ∫⁻ x : p → 𝔸 E, ‖D.slice x f‖ₑ
    _ ≤ _ := (lintegral_addOrbitMeasure_lintegral (H := New.ratVectors E p) (ν := .count)
        (D.continuous_slice f).enorm.measurable).ge
    _ < ⊤ := by
      refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨C * ‖f‖₊, fun x ↦ ?_⟩
      -- The points of `ratVectors` are the `toAdele ∘ ξ`.
      erw [lintegral_count, ← (ofInjective _ (toAdele (E := E)).injective.comp_left).tsum_eq]
      exact h_bound x

end MixedModelIntegrable

/-!
## Intertwining on the parabolic subgroup

The zero term ev = `New.Space.Splitting.zeroTerm` : 𝒮 V → 𝒮 V₀ is taken along the isotropic frame
`k` of a splitting.

`New.weilMultiplier` is the multiplier Δ in the definition of `ω`. `dataInner` is the scalar product
on `𝒮`.
-/

open Exchange MeasureTheory Matrix ComplexOrder WeilData Fock Finset Complex G Circle
  Heisenberg.IsVacuum

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {n₀ p : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) {g : G E s}
  (g₀ : G E s₀) (hi : D.iCoord * (g.adeleMatrix * D.iAdelic) = g₀.adeleMatrix) (a : GL p (𝔸 E))
  (hk : D.ActsOnFrame g a.val)

/-- For a in GL_p(𝔸) and x the point of the space `New.hyperbolicSpace` of p hyperbolic planes
(signs `hyperbolicSigns p`: +1 on the first p and −1 on the last p coordinates; x is (1, −1; 1,
1)/√2 at each infinite place and integral at the finite places), some g₁ in the adelic unitary group
has matrix x⁻¹ diag(a*⁻¹, a) x. Moreover Δ(g₁)υ(det a) is a nonnegative real number, where Δ is the
multiplier `weilMultiplier` and υ is the splitting character of the Weil data. -/
lemma exists_hyperbolic_levi_multiplier_nonneg :
    ∃ g₁ : G E (hyperbolicSigns p), 0 ≤ weilMultiplier g₁ * υ.val a.det ∧
      g₁.adeleMatrix = (hyperbolicSpace E p).x⁻¹.val * fromBlocks a⁻¹.valᴴ 0 0 a.val *
        (hyperbolicSpace E p).x := by
  let g₁ : G E (hyperbolicSigns p) :=
    (hyperbolicSpace E p).toRatCoords.symm
      ⟨blockGL (star a⁻¹, a), by simp [U, fromBlocks_conjTranspose,
      fromBlocks_map, star_eq_conjTranspose, fromBlocks_multiply, ← conjTranspose_mul]⟩
  have h_mat : g₁.adeleMatrix = (hyperbolicSpace E p).x⁻¹.1 * fromBlocks a⁻¹.1ᴴ 0 0 a.1 *
    (hyperbolicSpace E p).x := rfl
  refine ⟨g₁, ?_, h_mat⟩
  -- Both `weilMultiplier` and `υ` are products of factors at the infinite places and a finite
  -- factor.
  let a_fin : GL p (𝔸f E) := a.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
  have h_inf (w : NumberField.InfinitePlace E) :
      0 ≤ realMultiplier (g₁.1 w) * (a.det.val.1 w / ‖a.det.val.1 w‖) := by
    -- At `w` the frame `x` is `(1, -1; 1, 1) / √2`, so the lower right block of
    -- `x⁻¹ diag(a⁻¹ᴴ, a) x` is `(a⁻¹ᴴ + a) / 2`. Its adjoint times `a` is `(1 + aᴴ a) / 2`, whose
    -- determinant is nonnegative.
    have hx : (hyperbolicSpace E p).x.1.map (evalInf w) = (√2 : ℂ)⁻¹ • fromBlocks 1 (-1) 1 1 := rfl
    have hx_inv : (hyperbolicSpace E p).x⁻¹.1.map (evalInf w) = (√2 : ℂ)⁻¹ • fromBlocks 1 1 (-1)
      1 := rfl
    have h_lower : (g₁.adeleMatrix.map (evalInf w)).toBlocks₂₂ =
        (2 : ℂ)⁻¹ • ((a⁻¹.val.map (evalInf w))ᴴ + a.val.map (evalInf w)) := by
      have h_star : Function.Semiconj (evalInf w) star star := fun _ ↦ rfl
      simp only [h_mat, Matrix.map_mul, hx, hx_inv]
      simp [-coe_units_inv, fromBlocks_map, fromBlocks_smul, fromBlocks_multiply, smul_smul,
        conjTranspose_map (evalInf w) h_star, ← smul_add, ← mul_inv, ← Complex.ofReal_mul]
    have h_one : a⁻¹.val.map (evalInf w) * a.val.map (evalInf w) = 1 := by
      simp [← Matrix.map_mul, -coe_units_inv]
    have h_det : 0 ≤ (1 + (a.val.map (evalInf w))ᴴ * a.val.map (evalInf w)).det :=
      (PosSemidef.one.add (posSemidef_conjTranspose_mul_self _)).det_nonneg
    -- `realMultiplier` is the conjugate determinant of that block.
    have h_mult : realMultiplier (g₁.1 w) = star
      (g₁.adeleMatrix.map (evalInf w)).toBlocks₂₂.det := by
      let e_neg : {i // hyperbolicSigns p i = -1} ≃ p :=
        (Equiv.subtypeEquivRight (by simp)).trans Equiv.sumIsRight
      rw [realMultiplier, ← star_def, principalMinor, ← det_reindex_self e_neg]
      rfl
    rw [h_mult, h_lower, det_smul]
    simp [h_one, h_det, -coe_units_inv, ← det_conjTranspose, ← evalInf_apply, RingHom.map_det,
      add_mul, ← det_mul, field, div_nonneg]
  have h_fin :
      finMultiplier g₁.2 = ‖glMultiplier a_fin‖ ^ 2 * starRingEnd ℂ (chiFin a_fin.det) := by
    -- The finite part of `x` is integral, so only the two diagonal blocks count.
    have hx : (hyperbolicSpace E p).x.map (.snd ..) ∈ intGL (p ⊕ p) (Ô E) :=
      mem_intGL.2 (isOrthoIntegral_hyperbolicSpace.imp And.right And.right)
    change glMultiplier (GeneralLinearGroup.map (RingHom.snd ..)
      ((hyperbolicSpace E p).x⁻¹ * blockGL (star a⁻¹, a) * (hyperbolicSpace E p).x)) = _
    rw [map_mul, map_mul, map_inv, glMultiplier_mul_of_mem _ (inv_mem hx) hx,
      glMultiplier_fromBlocks (star a_fin⁻¹) a_fin (Equiv.refl _) (fromBlocks_map ..),
      glMultiplier_star_inv_mul]
  -- The idele `det a` has the valuations of its finite part `det a_fin`.
  rw [upsilon_eq_prod_mul_of_v_eq a_fin.det (by simp [a_fin, a.map_det]), weilMultiplier,
    mul_mul_mul_comm, ← prod_mul_distrib, h_fin]
  refine mul_nonneg (prod_nonneg fun w _ ↦ h_inf w) ?_
  -- In the finite factor, the phases of `conj (chiFin a_fin.det)` and of `υ` cancel.
  simp [chiFin, chiAdelic, field, ← coe_inv_eq_conj]

/-- Let `D` be a Witt decomposition V = (l E^p ⊕ k E^p) ⊥ i V₀, and for f in 𝒮(V) let
f[x] = `D.slice x f` in 𝒮(V₀) be its slice at x ∈ 𝔸^p. For f, f′ in 𝒮(V), the scalar product ⟨f[x],
f′[x]⟩ = ∫ conj(f[x]) f′[x] is integrable in x. -/
lemma integrable_dataInner_slice (f f' : 𝒮 V) :
    Integrable fun x : p → 𝔸 E ↦ V₀.dataInner (D.slice x f) (D.slice x f') := by
  -- `slice x f` is `zeroTerm` of a translate of `f`, which has norm `‖f‖`; so the integrand has
  -- norm at most `‖dataInner ∘ zeroTerm‖ * ‖f‖ * ‖slice x f'‖`
  refine ((D.integrable_slice f').norm.const_mul (‖V₀.dataInner ∘SL D.zeroTerm‖ * ‖f‖)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun x ↦ ?_)
  simpa [Heisenberg.Rep.norm_map, slice] using
    (V₀.dataInner ∘SL D.zeroTerm).le_opNorm₂ (V.ϱ (D.lAdelic *ᵥ x) f) (D.slice x f')

/-- For a Witt splitting `D` of `V` over `V₀` with frames of `p` columns, let f[x] = `D.slice x f`
in 𝒮(V₀) be the slice at x ∈ 𝔸^p. There is a constant C with ∫ ⟨f[x], f′[x]⟩ dx = C⟨f, f′⟩ for all
f, f′ in 𝒮(V). The pairing on the left is `dataInner` of 𝒮(V₀) and on the right that of 𝒮(V). -/
lemma integral_dataInner_slice :
    ∃ C : ℂ, ∀ f f' : 𝒮 V,
      ∫ x : p → 𝔸 E, V₀.dataInner (D.slice x f) (D.slice x f') = C * V.dataInner f f' := by
  -- The form on the left is invariant under the Heisenberg operators, hence a multiple of
  -- the scalar product.
  have h_inv (y : n → 𝔸 E) (f f' : 𝒮 V) :
      ∫ x, V₀.dataInner (D.slice x (V.ϱ y f)) (D.slice x (V.ϱ y f')) =
        ∫ x, V₀.dataInner (D.slice x f) (D.slice x f') := by
    -- `ϱ y` translates `x` by `lCoord *ᵥ y`, up to a character of modulus 1 and a unitary operator.
    rw [← integral_add_right_eq_self (fun x ↦ V₀.dataInner (D.slice x f) (D.slice x f'))
      (D.lCoord *ᵥ y)]
    simp [← mul_assoc]
  exact ⟨_, integral_form_eq_mul_modelInner
    (fun x ↦ V₀.dataInner.bilinearComp (D.slice x) (D.slice x))
    D.integrable_dataInner_slice h_inv⟩

include hk hi in
/-- Suppose g sends the frame k to k·a for some a in GL_p(𝔸), and g acts on the V₀-part as g₀. Then
there is a scalar c with ev(ω(g)f) = c·ω(g₀)(ev f) for all f in 𝒮(V), where ev is the zero term
`New.Space.Splitting.zeroTerm`. -/
lemma exists_zeroTerm_omega_eq_smul :
    ∃ c : ℂ, ∀ f : 𝒮 V, D.zeroTerm (V.ω g f) = c • V₀.ω g₀ (D.zeroTerm f) := by
  -- With `L = ω(g₀⁻¹) zeroTerm ω(g)`, the family `x ↦ L ϱ(lAdelic x)` obeys the same law as
  -- `slice`. At `ω(k) vacElem`, `k` adapted, both families are multiples of
  -- `‖vacuumFn x‖ ^ 2 • V₀.vacElem`, so they differ by a scalar; and the translates of
  -- `ω(k) vacElem` determine a bounded map (`ext_of_vacElem`).
  obtain ⟨k, h_adapted, -⟩ := D.exists_isAdapted_and_frame_eq 1
  let L : 𝒮 V →L[ℂ] 𝒮 V₀ := V₀.ω g₀⁻¹ ∘L D.zeroTerm ∘L V.ω g
  have hL_k (b : p → 𝔸 E) (f : 𝒮 V) : L (V.ϱ (D.kAdelic *ᵥ b) f) = L f := by
    simp_all [L, ← slice_zero, omega_rho]
  have hL_i (w : n₀ → 𝔸 E) (f : 𝒮 V) : L (V.ϱ (D.iAdelic *ᵥ w) f) = V₀.ϱ w (L f) := by
    simp [L, hi, ← adeleMatrix_mul, ← D.lCoord.mul_assoc, D.lCoord_mul_adeleMatrix hk, ← slice_zero,
      omega_rho,
      Matrix.mul_assoc]
  have h_law : D.IsMixedLaw fun x : p → 𝔸 E ↦ L ∘L V.ϱ (D.lAdelic *ᵥ x) :=
    D.isMixedLaw_comp_rho L hL_k hL_i
  obtain ⟨c', hc'_ne, hc'⟩ := h_adapted.slice_omega_vacElem
  obtain ⟨c, hc⟩ := h_adapted.exists_omega_vacElem_of_isMixedLaw h_law
  have hL : L = (c / c') • D.zeroTerm := by
    have hc_ratio (x : p → 𝔸 E) : (L ∘L V.ϱ (D.lAdelic *ᵥ x)) (V.ω k V.vacElem) =
        (c / c' * (c' * ‖vacuumFn ((1 : GL p (𝔸 E)).valᴴ *ᵥ x)‖ ^ 2)) • V₀.vacElem := by
      rw [hc, ← mul_assoc, div_mul_cancel₀ c hc'_ne]
    refine V.ext_of_vacElem k fun y ↦ ?_
    calc L (V.ω k (V.ϱ y V.vacElem))
      _ = (L ∘L V.ϱ (D.lAdelic *ᵥ 0)) (V.ϱ (k.adeleMatrix *ᵥ y) (V.ω k V.vacElem)) := by
        simp [omega_rho]
      _ = ((c / c') • D.zeroTerm) (V.ω k (V.ϱ y V.vacElem)) := by
        rw [h_law]
        simp [↓hc_ratio, hc', smul_smul, ← slice_zero, omega_rho, mul_left_comm]
  exact ⟨c / c', fun f ↦ by
    simpa [L, rep_apply_apply] using congrArg (V₀.ω g₀) (DFunLike.congr_fun hL f)⟩

omit [WeilData E] in
/-- The push-forward of the volume under `x ↦ aᴴ x` is `|det a|⁻¹` times the volume: for continuous
F on 𝔸^p, the integral of F(aᴴ x) is |det a|⁻¹ times the integral of F. -/
lemma integral_comp_conjTranspose_mulVec (a : GL p (𝔸 E)) {F : (p → 𝔸 E) → ℝ} (hF : Continuous F) :
    ∫ x : p → 𝔸 E, F (a.valᴴ *ᵥ x) = (ideleAbs a.det)⁻¹ * ∫ x : p → 𝔸 E, F x := by
  simpa [↓volume_map_mulVec_adele, star_eq_conjTranspose] using
    (integral_map (μ := volume) (φ := fun x ↦ (star a).val *ᵥ x) (by fun_prop)
      hF.aestronglyMeasurable).symm

/-- Let the group element k have as columns, reordered by e, those of the matrix of D's frames
times diag(x, 1) (`frameAt 1 1` is the matrix of the frames; x is the point of hyperbolic space),
and let g₁ have the matrix x⁻¹ diag(a*⁻¹, a) x. Then the conjugate by k of the Levi element of
(a, g₀) is block diagonal with blocks g₁, g₀, so its multiplier Δ is the product of theirs. -/
lemma weilMultiplier_conj_levi {k : G E s} {e : (p ⊕ p) ⊕ n₀ ≃ n} {g₁ : G E (hyperbolicSigns p)}
    (hs : s ∘ e = hyperbolicSigns p ⊕ᵥ s₀)
    (h_frame : D.frameAt 1 1 * fromBlocks (o := n₀) (hyperbolicSpace E p).x.val 0 0 1 =
      k.adeleMatrix.submatrix id e)
    (hg₁ : g₁.adeleMatrix = (hyperbolicSpace E p).x⁻¹.val * fromBlocks a⁻¹.valᴴ 0 0 a.val *
      (hyperbolicSpace E p).x) :
    weilMultiplier (k⁻¹ * D.levi (a, g₀) * k) = weilMultiplier g₁ * weilMultiplier g₀ := by
  have h_block :
      (D.levi (a, g₀)).adeleMatrix * (D.frameAt 1 1 * fromBlocks (o := n₀)
        (hyperbolicSpace E p).x.val 0 0 1) =
        D.frameAt 1 1 * fromBlocks ((hyperbolicSpace E p).x.val * g₁.adeleMatrix) 0 0
          g₀.adeleMatrix := by
    simp [hg₁, frameAt, ← Matrix.mul_assoc, fromCols_mul_fromBlocks, levi_mul_lAdelic,
      actsOnFrame_levi, levi_mul_iAdelic]
  have h_inv : k⁻¹.adeleMatrix.submatrix e id * k.adeleMatrix.submatrix id e = 1 := by
    simp [← submatrix_mul _ _ _ id _ Function.bijective_id, ← G.adeleMatrix_mul]
  refine weilMultiplier_fromBlocks hs ?_
  calc (k⁻¹ * D.levi (a, g₀) * k).adeleMatrix.submatrix e e
    _ = k⁻¹.adeleMatrix.submatrix e id * ((D.levi (a, g₀)).adeleMatrix * k.adeleMatrix.submatrix id
      e) := by
      simp [↓adeleMatrix_mul, submatrix_mul _ _ _ id, mul_assoc]
    _ = k⁻¹.adeleMatrix.submatrix e id * (k.adeleMatrix.submatrix id e * fromBlocks g₁.adeleMatrix 0
      0 g₀.adeleMatrix) := by
      simp [← h_frame, h_block, Matrix.mul_assoc, fromBlocks_multiply]
    _ = fromBlocks g₁.adeleMatrix 0 0 g₀.adeleMatrix := by
      rw [← Matrix.mul_assoc, h_inv, Matrix.one_mul]

/-- A scalar c with |c|² = |det a| and c J conj(m) = I, for reals I > 0, J ≥ 0 and a complex m with
m υ(det a) ≥ 0, is χ_𝔸(det a)⁻¹. -/
lemma eq_inv_chiAdelic_of_norm_sq_of_phase {c m : ℂ} {I J : ℝ} (hI : 0 < I) (hJ : 0 ≤ J)
    (h_abs : ‖c‖ ^ 2 = ideleAbs a.det) (h_phase : c * J * star m = I)
    (h_sign : 0 ≤ m * υ.val a.det) :
    c = (chiAdelic a.det)⁻¹ := by
  -- The signs make `c * υ(det a)` positive, so it is `‖c‖`.
  have h_pos : 0 < c * υ.val a.det := by
    refine pos_of_mul_pos_left (b := star (m * υ.val a.det)) ?_ (star_nonneg_iff.2 h_sign)
    have h_prod : 0 < c * star m * J := by rwa [mul_right_comm, h_phase, Complex.zero_lt_real]
    simpa [field, ← coe_inv_eq_conj] using pos_of_mul_pos_left h_prod (by positivity)
  have h_norm : ‖c‖ = c * υ.val a.det := by simpa [norm_coe] using norm_of_nonneg' h_pos.le
  simp [chiAdelic, ← h_abs, h_norm]

omit [WeilData E] in
/-- The Levi element attached to `(a, g₀)` sends the vector `l aᴴ x` to `l x`. -/
lemma levi_mulVec_lAdelic_mulVec_conjTranspose_mulVec (x : p → 𝔸 E) :
    (D.levi (a, g₀)).adeleMatrix *ᵥ D.lAdelic *ᵥ a.valᴴ *ᵥ x = D.lAdelic *ᵥ x := by
  simp [levi_mul_lAdelic, ← Matrix.mul_assoc, Matrix.mul_assoc D.lAdelic, ← conjTranspose_mul]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For the Levi element `D.levi (a, g₀)` attached to `a ∈ GL_p(𝔸)` and `g₀` in the group of `V₀`,
one has ev ω(`D.levi (a, g₀)`) = χ_𝔸(det a)⁻¹ ω(g₀) ev. Here ev is the zero term
`New.Space.Splitting.zeroTerm`, and `χ_𝔸 = υ |·|^(-1/2)`. -/
lemma zeroTerm_omega_levi (f : 𝒮 V) :
    D.zeroTerm (V.ω (D.levi (a, g₀)) f) = (chiAdelic a.det)⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  -- The scalar `c` of `exists_zeroTerm_omega_eq_smul` is found from `integral_dataInner_slice`
  -- for `u = ω(k) vacElem`, `k` adapted, and `v = ω(g) u`: the pair `(v, v)` gives
  -- `‖c‖ ^ 2 = |det a|`, the pair `(u, v)` gives its phase.
  set g : G E s := D.levi (a, g₀) with hg
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : 𝒮 V, D.zeroTerm (V.ω g f) = c • V₀.ω g₀ (D.zeroTerm f) :=
    D.exists_zeroTerm_omega_eq_smul g₀ (by simp [hg, levi_mul_iAdelic]) a (D.actsOnFrame_levi a g₀)
  obtain ⟨g₁, h_sign, hg₁⟩ := exists_hyperbolic_levi_multiplier_nonneg a
  obtain ⟨k, h_adapted, e, hs, h_frame⟩ := D.exists_isAdapted_and_frame_eq 1
  let u : 𝒮 V := V.ω k V.vacElem
  let v : 𝒮 V := V.ω g u
  let φ (x : p → 𝔸 E) : ℝ := ‖vacuumFn x‖ ^ 2
  obtain ⟨w, hw, hu⟩ : ∃ w ≠ (0 : ℂ), ∀ x, D.slice x u = (w * φ x) • V₀.vacElem := by
    simpa [φ] using h_adapted.slice_omega_vacElem
  -- The element `g` moves `l aᴴ x` to `l x`.
  have hv (x : p → 𝔸 E) : D.slice x v = c • V₀.ω g₀ (D.slice (aᴴ *ᵥ x) u) := by
    rw [slice, ContinuousLinearMap.comp_apply,
      ← D.levi_mulVec_lAdelic_mulVec_conjTranspose_mulVec g₀ a x, ← omega_rho]
    exact hc _
  obtain ⟨C, hC⟩ := D.integral_dataInner_slice
  -- The three pairings, with `I = ∫ φ²`, `J = ∫ φ(aᴴ x) φ(x)` and `∫ φ(aᴴ x)² = I / |det a|`.
  let I : ℝ := ∫ x, φ x * φ x
  let J : ℝ := ∫ x, φ (a.valᴴ *ᵥ x) * φ x
  have hI : 0 < I := by
    -- the integrand of the pair `(u, u)` has norm `‖w‖² φ²`, which is not zero at `0`
    simpa [hu, hw, φ, I, mul_mul_mul_comm ‖w‖, integral_const_mul] using
      integral_pos_of_integrable_nonneg_nonzero (x := 0) (by fun_prop)
        (D.integrable_dataInner_slice u u).norm (fun _ ↦ norm_nonneg _)
        (by simp [hu, hw, φ, vacuumFn])
  have hφ_cont : Continuous φ := (cont (adelicHeisenberg E 1)).norm.pow 2
  have h_scale : ∫ x, φ (a.valᴴ *ᵥ x) * φ (a.valᴴ *ᵥ x) = (ideleAbs a.det)⁻¹ * I :=
    integral_comp_conjTranspose_mulVec a (hφ_cont.mul hφ_cont)
  -- If the integrand of `hC` is `r * F x` with `F` real, the constant `r` comes out.
  have pair (f f' : 𝒮 V) {r : ℂ} {F : (p → 𝔸 E) → ℝ}
      (h : ∀ x : p → 𝔸 E, V₀.dataInner (D.slice x f) (D.slice x f') = r * F x) :
      r * (∫ x, F x : ℝ) = C * V.dataInner f f' := by
    simp [← hC, h, integral_const_mul, integral_complex_ofReal]
  have h_uu : w * star w * I = C := by
    refine (pair u u fun x ↦ ?_).trans (by simp [u])
    simp [hu]
    ring
  -- the scalar product of `u` and `ω(g) u` is `(conj weilMultiplier(k⁻¹gk))⁻¹`
  have h_coeff : V.dataInner u v = (star (weilMultiplier g₁ * weilMultiplier g₀))⁻¹ := by
    rw [← D.weilMultiplier_conj_levi g₀ a hs h_frame hg₁]
    exact V.dataInner_omega_vacElem_omega g k
  have h_uv : w * star w * c * (star (weilMultiplier g₀))⁻¹ * J = C * V.dataInner u v := by
    refine pair u v fun x ↦ ?_
    simp [hu, hv, dataInner_vacElem_omega_vacElem]
    ring
  have h_vv : w * star w * (c * star c) * ↑((ideleAbs a.det)⁻¹ * I) = C := by
    rw [← h_scale]
    refine (pair v v fun x ↦ ?_).trans (by simp [u, v])
    simp [hu, hv]
    ring
  rw [← h_uu] at h_vv
  rw [← h_uu, h_coeff] at h_uv
  have h_phase : c * J * star (weilMultiplier g₁) = I := by
    simpa [field, hw, weilMultiplier_ne_zero g₁, weilMultiplier_ne_zero g₀] using h_uv
  have h_abs : ‖c‖ ^ 2 = ideleAbs a.det := by
    simpa [field, mul_conj, hw, normSq_eq_norm_sq, -ofReal_pow] using h_vv
  rw [hc, eq_inv_chiAdelic_of_norm_sq_of_phase a hI (integral_nonneg fun x ↦ by positivity) h_abs
    h_phase h_sign]

/-- The Levi element with parts `a` (on the isotropic frame) and `g₀` (on `V₀`) acts on the slices
`x ↦ D.slice x f` by the substitution `x ↦ aᴴ x`, the operator `ω(g₀)` on the values and the
factor `(chiAdelic a.det)⁻¹`. -/
lemma slice_omega_levi (x : p → 𝔸 E) (f : 𝒮 V) :
    D.slice x (V.ω (D.levi (a, g₀)) f) =
      (chiAdelic a.det)⁻¹ • V₀.ω g₀ (D.slice (a.valᴴ *ᵥ x) f) := by
  have h_point : (D.levi (a, g₀)).adeleMatrix *ᵥ D.lAdelic *ᵥ a.valᴴ *ᵥ x = D.lAdelic *ᵥ x :=
    D.levi_mulVec_lAdelic_mulVec_conjTranspose_mulVec g₀ a x
  calc D.slice x (V.ω (D.levi (a, g₀)) f)
    _ = D.zeroTerm (V.ω (D.levi (a, g₀)) (V.ϱ (D.lAdelic *ᵥ a.valᴴ *ᵥ x) f)) := by
      rw [omega_rho, h_point, slice, ContinuousLinearMap.comp_apply]
    _ = _ := D.zeroTerm_omega_levi g₀ a _

include hi in
/-- Let `D` split `V` as `(l E^p ⊕ k E^p) ⊥ ι V₀`, and let `g` satisfy gk = ka for a p×p adelic
matrix a whose determinant is the idele d. Suppose also that the V₀-block of g is g₀ in the adelic
group of V₀. Then ev(ω(g)f) = υ(d)⁻¹ |d|^{1/2} ω(g₀) ev(f) for all f, where ev is the zero term
along k, υ is the splitting character of the Weil data, and the scalar is the inverse of
χ_𝔸(d) = υ(d)|d|^{−1/2}. The V₀-block is `iCoord * g * iAdelic`, with `iAdelic` the adelic embedding
ι of V₀ and `iCoord` the projection to its coordinates. When V₀ is zero, this is the value at the
origin of the formula for the Siegel parabolic subgroup in the Schrödinger model. -/
lemma zeroTerm_omega {a : Matrix p p (𝔸 E)} (hk : D.ActsOnFrame g a) (d : (𝔸 E)ˣ)
    (h_det : a.det = d.val) (f : 𝒮 V) :
    D.zeroTerm (V.ω g f) = (chiAdelic d)⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  -- Write `g = radicalElement c b * levi (a, g₀)`. The Levi factor is `zeroTerm_omega_levi`; the
  -- scalar by which `radicalElement c b` acts on `zeroTerm` is trivial, because
  -- `radicalElement c b` is a commutator (`exists_levi_mul_radicalElement_eq`).
  obtain ⟨c, b, a', g₀', rfl, rfl, hg₀⟩ := D.exists_eq_radicalElement_mul_levi hk
  obtain rfl : a'.det = d := Units.ext h_det
  obtain rfl : g₀' = g₀ := ext_adeleMatrix (hg₀.trans hi)
  have h_scalar (b₁ : Matrix p p (𝔸 E)) :
      ∃ z : ℂ, ∀ u : 𝒮 V, D.zeroTerm (V.ω (D.radicalElement c b₁) u) = z • D.zeroTerm u := by
    obtain ⟨h_frame, h_block⟩ : D.ActsOnFrame (D.radicalElement c b₁) 1 ∧
        D.iCoord * ((D.radicalElement c b₁).adeleMatrix * D.iAdelic) = 1 :=
      D.exists_eq_radicalElement_iff.1 ⟨c, b₁, rfl⟩
    simpa using D.exists_zeroTerm_omega_eq_smul 1 (h_block.trans adeleMatrix_one.symm) 1 h_frame
  choose z hz using h_scalar
  obtain ⟨t, b', h_comm⟩ : ∃ (t : GL p (𝔸 E)) (b' : Matrix p p (𝔸 E)),
      D.levi (t, 1) * D.radicalElement c b' = D.radicalElement c b' * D.radicalElement c b * D.levi
        (t, 1) :=
    D.exists_levi_mul_radicalElement_eq c b
  let m : G E s := D.levi (t, 1) * D.radicalElement c b'
  -- Both sides are `zeroTerm u` times the product of `z b`, `z b'` and `(chiAdelic t.det)⁻¹`.
  have h_unip (u : 𝒮 V) : D.zeroTerm (V.ω (D.radicalElement c b * m) u) = D.zeroTerm (V.ω m u) :=
    calc D.zeroTerm (V.ω (D.radicalElement c b * m) u)
      _ = z b' • z b • (chiAdelic t.det)⁻¹ • D.zeroTerm u := by
        simp [m, hz, zeroTerm_omega_levi, smul_comm (z b')]
      _ = D.zeroTerm (V.ω m u) := by
        simp [m, h_comm, hz, zeroTerm_omega_levi]
  -- `ω m` is onto, so `radicalElement c b` can be dropped in front of the Levi factor too.
  rw [← zeroTerm_omega_levi]
  simpa only [rep_apply_apply, mul_assoc, mul_inv_cancel_left] using
    h_unip (V.ω (m⁻¹ * D.levi (a', g₀')) f)

/-- For a Witt splitting `D` of `V` over `V₀` with frames of `p` columns and a hermitian adelic
`p × p` matrix `z`, consider the element `D.radicalElement 0 z` of the centre of the radical. It
fixes `k`, fixes `ι`, and sends `l` to `l − k j⁻¹ z`. Acting through the Weil representation `V.ω`,
it multiplies the slice `D.slice x f = ev(ϱ(lx) f)` in 𝒮(V₀) by the standard additive character at
`-xᴴ z x / 2`. -/
lemma slice_omega_radicalElement_zero {z : Matrix p p (𝔸 E)} (hz : zᴴ = z) (x : p → 𝔸 E) (f : 𝒮 V) :
    D.slice x (V.ω (D.radicalElement 0 z) f) =
      (stdAddChar E (-(toAdele (2⁻¹ : E) * star x ⬝ᵥ z *ᵥ x)) : ℂ) • D.slice x f := by
  -- The element fixes the zero term, and it sends `l x + k (j⁻¹ z x)` to `l x`.
  let y : n → 𝔸 E := D.lAdelic *ᵥ x + D.kAdelic *ᵥ (toAdele (j⁻¹ : E) • z *ᵥ x)
  have h_mat : (D.radicalElement 0 z).adeleMatrix = 1 - D.kAdelic * (toAdele (j⁻¹ : E) • z) *
    D.lCoord := by
    simp [radicalElement, hz, smul_smul, ← two_smul (𝔸 E), ← map_ofNat (toAdele (E := E)) 2,
      ← map_mul,
      mul_left_comm (2⁻¹ : E)]
  have h_point : (D.radicalElement 0 z).adeleMatrix *ᵥ y = D.lAdelic *ᵥ x := by
    simp [y, h_mat, mulVec_add, sub_mulVec, Matrix.sub_mul, Matrix.mul_assoc, mulVec_smul,
      smul_mulVec]
  obtain ⟨h_frame, h_block⟩ : D.ActsOnFrame (D.radicalElement 0 z) 1 ∧
      D.iCoord * ((D.radicalElement 0 z).adeleMatrix * D.iAdelic) = 1 :=
    D.exists_eq_radicalElement_iff.1 ⟨0, z, rfl⟩
  have h_fix (f' : 𝒮 V) : D.zeroTerm (V.ω (D.radicalElement 0 z) f') = D.zeroTerm f' := by
    simpa using D.zeroTerm_omega 1 (h_block.trans adeleMatrix_one.symm) h_frame 1 (by simp) f'
  have h_coeff : (j / 2 * j⁻¹ : E) = 2⁻¹ := by field [j_ne_zero]
  calc D.slice x (V.ω (D.radicalElement 0 z) f)
    _ = D.zeroTerm (V.ω (D.radicalElement 0 z) (V.ϱ y f)) := by
      rw [omega_rho, h_point, slice, ContinuousLinearMap.comp_apply]
    _ = (adelicHeisenberg E 1).β x (toAdele (j⁻¹ : E) • z *ᵥ x) • D.slice x f := by
      rw [h_fix, ← slice_zero, D.isMixedLaw_slice]
      simp [y, mulVec_add, mulVec_mulVec, mulVec_smul]
    _ = _ := by
      simp [adelicHeisenberg, star_mulVec, hz, ← dotProduct_mulVec, star_j, ← mul_assoc, ← map_mul,
        h_coeff]

end New.Space.Splitting

namespace New.Space

/-! ## Invariance of θ under rational points -/

section RationalInvariance

open Matrix Splitting Exchange

variable {E : Type*} [Field E] [CMType E] {n p : Type*} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} [Fintype p] [WeilData E]

variable (V) in
/-- The subgroup of the rational unitary γ whose Weil operator ω(γ) fixes the theta functional of
V. -/
noncomputable def thetaStabilizer : Subgroup (U V.J) where
  carrier := {γ : U V.J | ∀ f : 𝒮 V, V.θ (V.ω (V.ratEmbed γ) f) = V.θ f}
  one_mem' f := by simp
  mul_mem' {γ δ} hγ hδ f := by rw [map_mul, ← rep_apply_apply, hγ, hδ]
  inv_mem' {γ} hγ f := by simpa [rep_apply_apply] using (hγ (V.ω (V.ratEmbed γ⁻¹) f)).symm

/-- Let V be split by D, with isotropic frames k, l and no middle part. A rational unitary γ that
maps the span of k to itself, γk = ka with a invertible over E, fixes the theta functional θ of V:
θ(ω(γ)f) = θ(f), where ω is the Weil representation and γ acts through the rational embedding. -/
lemma theta_omega_ratEmbed_of_mul_k (γ : U V.J) [DecidableEq p]
    (D : V.Splitting (stdSpace E Empty) p) (a : GL p E) (hk : γ.val.val * D.k = D.k * a.val)
    (f : 𝒮 V) :
    V.θ (V.ω (V.ratEmbed γ) f) = V.θ f := by
  -- Expand `θ (ω γ f)` along the splitting `D' = γ D` and `θ f` along `D` as sums over `x ∈ E^p`
  -- (`hasSum_theta_slice`): the terms agree.
  let D' : V.Splitting (stdSpace E Empty) p :=
    splittingOfGram (γ.val.val * ((D.l.fromCols D.k).fromCols D.i))
      ((U.gram_invariant γ _ _).trans D.gram_eq_hyperbolicSum) D.card_eq
  have h_l' : D'.lAdelic = (V.ratEmbed γ).adeleMatrix * D.lAdelic := by
    simp [adeleMatrix_ratEmbed, lAdelic, D', splittingOfGram, Matrix.mul_assoc]
  -- `γ` keeps the span of `D.k`, so `D'` and `D` have the same zero-term map. The middle part has
  -- no coordinates, so the conditions on it are empty.
  have h_k' : D'.k = D.k * a.val := by simp [← hk, D', splittingOfGram]
  have h_ev : D'.zeroTerm = D.zeroTerm :=
    D.zeroTerm_congr D' (by simp [h_k', ← Matrix.mul_assoc]) (Subsingleton.elim _ _)
  -- The adelic matrix of `γ` is `x⁻¹ γ x`, so it acts on `D.kAdelic = x⁻¹ k` by `a`.
  have h_frame : D.ActsOnFrame (V.ratEmbed γ) (a.map (toAdele (E := E))).val := by
    simp [ActsOnFrame, adeleMatrix_ratEmbed, kAdelic, Matrix.mul_assoc, ← Matrix.map_mul, hk]
  -- `ω γ` changes the zero term by `(chiAdelic (det a))⁻¹`, which is `1` as `det a` is rational.
  have h_law (f' : 𝒮 V) : D.zeroTerm (V.ω (V.ratEmbed γ) f') = D.zeroTerm f' := by
    simpa [GeneralLinearGroup.map_det, chiAdelic, upsilon_toAdele, ideleAbs_toAdele] using
      D.zeroTerm_omega 1 (Subsingleton.elim _ _) h_frame (a.map toAdele).det rfl f'
  have h_term (x : p → 𝔸 E) : D'.slice x (V.ω (V.ratEmbed γ) f) = D.slice x f := by
    simp [slice, h_ev, h_l', ← mulVec_mulVec, ← omega_rho, h_law]
  refine (D'.hasSum_theta_slice _).unique ?_
  simpa only [h_term] using D.hasSum_theta_slice f

/-- If V has a splitting with no middle part, every point γ of the rational unitary group fixes the
theta functional θ under the Weil representation ω: θ(ω(γ)f) = θ(f). -/
lemma theta_omega_ratEmbed_of_splitting (γ : U V.J) [DecidableEq p]
    (D : V.Splitting (stdSpace E Empty) p) (f : 𝒮 V) :
    V.θ (V.ω (V.ratEmbed γ) f) = V.θ f := by
  -- The stabilizer of `θ` contains two opposite parabolic subgroups, which generate the group.
  have h_le (D' : V.Splitting (stdSpace E Empty) p) : D'.siegelParabolic ≤ V.thetaStabilizer :=
    fun δ ⟨a, ha⟩ ↦ theta_omega_ratEmbed_of_mul_k δ D' a ha
  have h_top : V.thetaStabilizer = ⊤ := by
    rw [eq_top_iff, ← D.siegelParabolic_sup_symm_eq_top]
    exact sup_le (h_le D) (h_le D.symm)
  have h_mem : γ ∈ V.thetaStabilizer := by simp [h_top]
  exact h_mem f

variable (V) in
/-- The splitting without middle part of `V ⊕ V⁻`, with `V⁻` the space of the negative form, whose
frame `k` spans the diagonal `{(v, v)}` and whose frame `l` spans the antidiagonal `{(v, -v)}`. -/
noncomputable def diagonalSplitting : (V.sum V.neg).Splitting (stdSpace E Empty) n where
  k := fromRows 1 1
  l := fromRows ((2⁻¹ : E) • V.J⁻¹) (-((2⁻¹ : E) • V.J⁻¹))
  i := 0
  gram_kk := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
  gram_ll := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows, V.isHermitian_J.inv.eq]
  gram_lk := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows, V.isHermitian_J.inv.eq, ← two_smul E,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 V.isUnit_J)]
  gram_ii := Subsingleton.elim _ _
  gram_ik := by simp
  gram_il := by simp
  card_eq := by simp [two_mul]

variable {m : Type*} [Fintype m] [DecidableEq m] {t : m → ℤˣ} {V' : Space E m t}

/-- For a datum y of a second space V′, the functional f ↦ θ(f ⊠ y) is a multiple of the theta
functional of V. Here θ is the theta functional of V ⊕ V′, and ⊠ = `New.Space.boxProd` is the
tensor product 𝒮(V) × 𝒮(V′) → 𝒮(V ⊕ V′) for the evident splitting of the coordinates. -/
lemma exists_theta_boxProd_eq_mul (y : 𝒮 V') :
    ∃ c : ℂ, ∀ f : 𝒮 V, (V.sum V').θ (boxProd signs_comp_refl f y) = c * V.θ f := by
  -- It is invariant under the rational `ϱ x` of `V`, which act as `ϱ (x, 0)` on `V ⊕ V'`.
  let ℓ : 𝒮 V →L[ℂ] ℂ := (V.sum V').rawTheta ∘L (boxProd signs_comp_refl).flip y
  have h_sum : (V.sum V').IsRatInvariant (V.sum V').rawTheta :=
    (V.sum V').isThetaFunctional_rawTheta.left
  have h_inv : V.IsRatInvariant ℓ := by
    rintro _ ⟨x, rfl⟩ (f : 𝒮 V)
    have h_act : boxProd signs_comp_refl (V.ϱ (V.vecAtPoint x) f) y =
        (V.sum V').ϱ ((V.sum V').vecAtPoint (x ⊕ᵥ 0)) (boxProd signs_comp_refl f y) := by
      rw [sum_vecAtPoint, rho_boxProd]
      simp [Function.comp_def, ← Pi.zero_def]
    calc ℓ (V.ϱ (V.vecAtPoint x) f)
      _ = (V.sum V').rawTheta
            ((V.sum V').ϱ ((V.sum V').vecAtPoint (x ⊕ᵥ 0)) (boxProd signs_comp_refl f y)) :=
        congrArg (V.sum V').rawTheta h_act
      _ = ℓ f := h_sum _ ⟨x ⊕ᵥ 0, rfl⟩ _
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ℓ = c • V.rawTheta := V.isThetaFunctional_rawTheta.eq_smul h_inv
  exact ⟨c, fun f ↦ by simpa [ℓ, theta_eq_rawTheta] using DFunLike.congr_fun hc f⟩

variable (V V') in
/-- The theta functional of V ⊕ V′ does not vanish on all products f ⊠ y (`New.Space.boxProd`) of
data f of V and y of V′. -/
lemma exists_theta_boxProd_ne_zero :
    ∃ (f : 𝒮 V) (y : 𝒮 V'), (V.sum V').θ (boxProd signs_comp_refl f y) ≠ 0 := by
  -- Otherwise the theta function of the vacuum `vacElem ⊠ vacElem` would vanish at every point.
  by_contra! h_zero
  have h_vac : (V.sum V').vacElem = 0 := by
    ext x
    rw [← theta_rho, ← boxProd_vacElem (V₁ := V) (V₂ := V') signs_comp_refl, rho_boxProd, h_zero,
      zero_apply]
  simpa [h_vac] using (V.sum V').dataInner_vacElem_vacElem

/-- The theta functional is invariant under rational points: θ(ω(γ)f) = θ(f) for every γ in the
rational unitary group of V and every f in 𝒮(V), where ω is the Weil representation.

A case of Weil's invariance of the theta distribution under rational points, for the unitary group
of a hermitian space V with a point, with the representation ω and the functional θ on 𝒮(V). -/
lemma theta_omega_ratEmbed (γ : U V.J) (f : 𝒮 V) : V.θ (V.ω (V.ratEmbed γ) f) = V.θ f := by
  -- Doubling. The space `W = V ⊕ V⁻` is split, so `(γ, 1)` fixes its theta functional, and with it
  -- the functionals `θ (· ⊠ y)`. These are multiples of the `θ` of `V`, not all zero.
  let W : Space E (n ⊕ n) (s ⊕ᵥ -s) := V.sum V.neg
  obtain ⟨f₀, y, h_ne⟩ := exists_theta_boxProd_ne_zero V V.neg
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f' : 𝒮 V, W.θ (boxProd signs_comp_refl f' y) = c * V.θ f' :=
    exists_theta_boxProd_eq_mul y
  have h_act : W.ω (W.ratEmbed (U.sum rfl (γ, 1))) (boxProd signs_comp_refl f y) =
      boxProd signs_comp_refl (V.ω (V.ratEmbed γ) f) y := by
    rw [sum_ratEmbed, omega_boxProd signs_comp_refl (G.adeleMatrix_sum _)]
    simp
  refine mul_left_cancel₀ (left_ne_zero_of_mul (by rwa [hc] at h_ne) : c ≠ 0) ?_
  calc c * V.θ (V.ω (V.ratEmbed γ) f)
    _ = W.θ (W.ω (W.ratEmbed (U.sum rfl (γ, 1))) (boxProd signs_comp_refl f y)) := by
      rw [h_act, hc]
    _ = W.θ (boxProd signs_comp_refl f y) :=
      theta_omega_ratEmbed_of_splitting _ V.diagonalSplitting _
    _ = c * V.θ f := hc f

/-- A rational point γ acts on a datum f, read as the function f(x) = θ(ϱ(x)f) of the adelic vector
x, by substitution: (ω(γ)f)(x) = f(γ⁻¹x). -/
lemma omega_ratEmbed_apply (γ : U V.J) (f : 𝒮 V) (x : n → 𝔸 E) :
    V.ω (V.ratEmbed γ) f x = f ((V.ratEmbed γ)⁻¹.adeleMatrix *ᵥ x) := by
  rw [← theta_rho, ← theta_rho, ← theta_omega_ratEmbed γ (V.ϱ _ f), omega_rho]
  simp [← G.adeleMatrix_mul]

end RationalInvariance

end New.Space

end
