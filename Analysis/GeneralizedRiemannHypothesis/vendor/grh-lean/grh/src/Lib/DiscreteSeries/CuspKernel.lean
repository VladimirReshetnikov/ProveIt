import Lib.Adelic.Reduction.FirstMinimumShortBases
import Lib.General.LinearAlgebra.HermitianMatrices

/-!
# Kernels kill bounded radical-invariant functions; dilations along isotropic subspaces

The file proves that, under hypotheses stated below, integration against an idempotent kernel kills
bounded continuous functions that are left invariant under a radical, namely the elements `r` with
`(r, 1) ∈ D` for a subgroup `D` of `G × ℂˣ`
(`New.DiscreteSeries.integral_idempotentKernel_mul_eq_zero`). It also proves that, for unitary
groups, dilations along an isotropic subspace meet every conjugate of a neighbourhood of `1`
(`New.DiscreteSeries.exists_conj_mem_dilationGroup`). The second result is used for the hypothesis
`hD_near` of the first.

The imported notions used in the statements are:
* `IsIdempotentKernel e`: `e` is continuous, integrable and self-adjoint, `e 1 ≠ 0`, and the
  convolution `e * δ_x * e` is `(e x⁻¹ / e 1) • e`;
* `U J`: the group of invertible matrices `g` with `gᴴ * J * g = J`;
* `dilationGroup A`: the pairs `(g, c)` with `g ∈ U J` and `c` a unit, such that `g * A = c • A`
  and `wᴴ * J * g * v = wᴴ * J * v` whenever the columns of `v` and `w` are `J`-orthogonal to
  those of `A`.

## Relation to the literature

Known result: coefficients of integrable discrete series are cusp forms. The vanishing of constant
terms is proved for any continuous self-adjoint integrable minimal idempotent `e` with `‖e‖ * ℓ`
integrable, tested on bounded continuous functions invariant under the radical, under the
hypotheses on `H`, `ℓ` and `D` stated below. Source: R. Godement, C. R. Acad. Sci. Paris 225
(1947) 521-523, 657-659; N. Wallach, Real Reductive Groups I (1988), ch. 7; the closest to the proof
here are B. Barnes, Proc. Edinburgh Math. Soc. 23 (1980), and A. Valette, Math. Ann. 294 (1992)
277-287.
-/

/-!
## A kernel kills bounded functions left invariant under a radical

`New.DiscreteSeries.integral_idempotentKernel_mul_eq_zero` is the abstract form of the vanishing of
constant terms that makes forms cuspidal. In the application `D` consists of dilations along an
isotropic subspace paired with their scale factors, and `H` is a logarithmic height.
-/

section KernelVanishing

open MeasureTheory Complex BoundedContinuousFunction

namespace New.DiscreteSeries

/-- An element `X` of a normed algebra that anticommutes with an element `U` within `1 / 2` of
`1` is zero. -/
lemma eq_zero_of_anticommute {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] {U X : A}
    (hU : ‖1 - U‖ ≤ 1 / 2) (h_anti : U * X = -(X * U)) : X = 0 := by
  have h_two : (2 : ℂ) • X = (1 - U) * X + X * (1 - U) := by
    simp [mul_sub, h_anti, two_smul, sub_mul]
  have h_le : ‖(2 : ℂ) • X‖ ≤ 1 / 2 * ‖X‖ + ‖X‖ * (1 / 2) := by
    grw [h_two, norm_add_le, norm_mul_le, norm_mul_le, hU]
  rw [norm_smul, norm_ofNat] at h_le
  exact norm_le_zero_iff.mp (by linarith)

/-- The product of an integrable function `k` with a translate of a bounded continuous function
`φ` is integrable. -/
lemma integrable_mul_translate {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasureSpace G] [BorelSpace G] {k : G → ℂ} (hk : Integrable k)
    (φ : G →ᵇ ℂ) (y : G) : Integrable fun g : G ↦ k g * φ (y * g) :=
  hk.mul_bdd (c := ‖φ‖) (by fun_prop) (by simp [norm_coe_le_norm])

/-- The integral of an integrable function `k` against a translate of a bounded continuous
function `φ` is at most the `L¹` norm of `k` times the supremum norm of `φ`. -/
lemma norm_integral_mul_translate_le {G : Type*} [Group G] [TopologicalSpace G] [MeasureSpace G]
    {k : G → ℂ} (hk : Integrable k) (φ : G →ᵇ ℂ) (y : G) :
    ‖∫ g : G, k g * φ (y * g)‖ ≤ ‖hk.toL1‖ * ‖φ‖ := by
  rw [L1.norm_of_fun_eq_integral_norm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hk.norm.mul_const ‖φ‖) (.of_forall fun g ↦ ?_)
  simp [norm_coe_le_norm, mul_le_mul_of_nonneg_left]

/-- The integrals of an integrable function `e` against the translates of `φ` by `y` and by `y * b`
differ by at most the `L¹` distance of `e` and its translate by `b`, times the norm of `φ`. -/
lemma norm_integral_mul_translate_sub_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasureSpace G] [BorelSpace G]
    [(volume (α := G)).IsMulLeftInvariant] {e : G → ℂ} (he : Integrable e) (φ : G →ᵇ ℂ) (y b : G) :
    ‖(∫ g : G, e g * φ (y * g)) - ∫ g : G, e g * φ (y * b * g)‖ ≤
      ‖(he.sub (he.comp_mul_left b⁻¹)).toL1‖ * ‖φ‖ := by
  have h_subst : ∫ g : G, e g * φ (y * b * g) = ∫ g : G, e (b⁻¹ * g) * φ (y * g) := by
    simpa [mul_assoc] using integral_mul_left_eq_self (fun g : G ↦ e (b⁻¹ * g) * φ (y * g)) b
  rw [h_subst, ← integral_sub (integrable_mul_translate he φ y)
    (integrable_mul_translate (he.comp_mul_left b⁻¹) φ y)]
  simpa [sub_mul] using norm_integral_mul_translate_le (he.sub (he.comp_mul_left b⁻¹)) φ y

/-- If `H (y * g)` differs from `H y` by at most `ℓ g`, then the integral of `e` against
`φ (y * g)` times the variation of the phase `circleMap 0 1 (H * θ)`, that is `exp (i H θ)`, is at
most `|θ|` times the integral of `‖e‖ * ℓ` times the norm of `φ`. -/
lemma norm_integral_mul_phase_sub_le {G : Type*} [Group G] [TopologicalSpace G] [MeasureSpace G]
    {e : G → ℂ} {H ℓ : G → ℝ} (hℓ : Integrable fun g : G ↦ ‖e g‖ * ℓ g)
    (hH_lip : ∀ y g : G, |H (y * g) - H y| ≤ ℓ g) (θ : ℝ) (φ : G →ᵇ ℂ) (y : G) :
    ‖∫ g : G, e g * ((circleMap 0 1 (H (y * g) * θ) - circleMap 0 1 (H y * θ)) * φ (y * g))‖ ≤
      |θ| * (∫ g : G, ‖e g‖ * ℓ g) * ‖φ‖ := by
  rw [← integral_const_mul, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((hℓ.const_mul |θ|).mul_const ‖φ‖) (.of_forall fun g ↦ ?_)
  have h_phase : ‖circleMap 0 1 (H (y * g) * θ) - circleMap 0 1 (H y * θ)‖ ≤ |θ| * ℓ g := by
    grw [(lipschitzWith_circleMap 0 1).norm_sub_le, ← hH_lip y g]
    simp [mul_comm _ θ, ← mul_sub]
  grw [norm_mul, norm_mul, φ.norm_coe_le_norm, h_phase]
  exact le_of_eq (by ring)

/-- Integrating the right translates of `φ` against an integrable function `e` is a bounded
operator on the bounded continuous functions. -/
lemma exists_kernel_operator {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasureSpace G] [BorelSpace G] {e : G → ℂ} (he : Integrable e) :
    ∃ T : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ, ∀ (φ : G →ᵇ ℂ) (y : G), T φ y = ∫ g : G, e g * φ (y * g) := by
  have h_cont (φ : G →ᵇ ℂ) : Continuous fun y : G ↦ ∫ g : G, e g * φ (y * g) :=
    continuous_of_dominated (by fun_prop) (by simp [norm_coe_le_norm, mul_le_mul_of_nonneg_left])
      (he.norm.mul_const ‖φ‖) (.of_forall (by fun_prop))
  let T : (G →ᵇ ℂ) →ₗ[ℂ] G →ᵇ ℂ :=
    { toFun φ := ofNormedAddCommGroup _ (h_cont φ) _ (norm_integral_mul_translate_le he φ)
      map_add' := by simp [integrable_mul_translate he, integral_add, mul_add, DFunLike.ext_iff]
      map_smul' := by simp [mul_left_comm, integral_const_mul, DFunLike.ext_iff] }
  have hT (φ : G →ᵇ ℂ) : ‖T φ‖ ≤ ‖he.toL1‖ * ‖φ‖ :=
    norm_le_of_nonempty.mpr (norm_integral_mul_translate_le he φ)
  exact ⟨T.mkContinuous ‖he.toL1‖ hT, fun _ _ ↦ rfl⟩

/-- Integration against a minimal idempotent kernel `e` (continuous, integrable, self-adjoint, with
`e * δ_x * e` a multiple of `e`) is an idempotent operator. -/
lemma kernel_operator_idempotent {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [MeasureSpace G] [BorelSpace G]
    [(volume (α := G)).IsHaarMeasure] {e : G → ℂ} (h_ker : IsIdempotentKernel e)
    {T : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ}
    (hT : ∀ (φ : G →ᵇ ℂ) (y : G), T φ y = ∫ g : G, e g * φ (y * g)) (φ : G →ᵇ ℂ) :
    T (T φ) = T φ := by
  ext y
  have h_bounded : IsBoundedMeasurable fun g : G ↦ φ (y * g) :=
    .of_continuous ⟨‖φ‖, fun g ↦ φ.norm_coe_le_norm (y * g)⟩
  -- The associativity of convolution, applied to `e * e * φ`.
  calc T (T φ) y
    _ = ∫ x : G, e x * ∫ g : G, e g * φ (y * (x * g)) := by simp only [hT, mul_assoc]
    _ = ∫ g : G, (∫ x : G, e x * e (x⁻¹ * g)) * φ (y * g) :=
      integral_smul_integral_eq_integral_conv_smul id h_ker.integrable h_ker.integrable h_bounded
    _ = T φ y := by simp only [h_ker.convolution_self, hT]

/-- Left translation by `a`, where `(a, z) ∈ D`, preserves the space `V` of the functions fixed by
the kernel operator `T` and left invariant under the elements `r` with `(r, 1) ∈ D`. -/
lemma exists_left_translation_operator {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasureSpace G] {e : G → ℂ} {T : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ}
    (hT : ∀ (φ : G →ᵇ ℂ) (y : G), T φ y = ∫ g : G, e g * φ (y * g))
    {D : Subgroup (G × ℂˣ)} {V : Submodule ℂ (G →ᵇ ℂ)}
    (hV : ∀ φ : G →ᵇ ℂ, φ ∈ V ↔ T φ = φ ∧ ∀ r : G, (r, 1) ∈ D → ∀ g : G, φ (r * g) = φ g)
    {a : G} {z : ℂˣ} (ha : (a, z) ∈ D) :
    ∃ U : V →L[ℂ] V, ∀ (φ : V) (y : G), (U φ).1 y = φ.1 (a * y) := by
  refine ⟨(compContinuousCLM _ _ (.mulLeft a)).restrict fun φ hφ ↦ ?_, fun _ _ ↦ rfl⟩
  obtain ⟨h_fix, h_inv⟩ := (hV φ).1 hφ
  refine (hV _).2 ⟨ext fun y ↦ ?_, fun r hr g ↦ ?_⟩
  · simpa [hT, mul_assoc] using DFunLike.congr_fun h_fix (a * y)
  · have h_conj : (a * r * a⁻¹, 1) ∈ D := by simpa using mul_mem (mul_mem ha hr) (inv_mem ha)
    simpa [mul_assoc] using h_inv (a * r * a⁻¹) h_conj (a * g)

/-- Let `D` be a subgroup of `G × ℂˣ` and `V` the space of functions fixed by the kernel operator
`T` and invariant under the radical, the `r` with `(r, 1) ∈ D`. If `(a, z) ∈ D` and for every `y`
some `b y` with `(y * b y * y⁻¹, z) ∈ D` translates `e` by less than `1 / 2` in `L¹`, then the
translation `U` of `V` by `a` is within `1 / 2` of the identity. -/
lemma norm_one_sub_left_translation_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasureSpace G] [BorelSpace G]
    [(volume (α := G)).IsMulLeftInvariant] {e : G → ℂ}
    (he : Integrable e) {T : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ}
    (hT : ∀ (φ : G →ᵇ ℂ) (y : G), T φ y = ∫ g : G, e g * φ (y * g))
    {D : Subgroup (G × ℂˣ)} {V : Submodule ℂ (G →ᵇ ℂ)}
    (hV : ∀ φ : G →ᵇ ℂ, φ ∈ V ↔ T φ = φ ∧ ∀ r : G, (r, 1) ∈ D → ∀ g : G, φ (r * g) = φ g)
    {a : G} {z : ℂˣ} (ha : (a, z) ∈ D) {b : G → G} (hb : ∀ y : G, (y * b y * y⁻¹, z) ∈ D)
    (hb_dist : ∀ y : G, ‖(he.sub (he.comp_mul_left (b y)⁻¹)).toL1‖ < 1 / 2)
    {U : V →L[ℂ] V} (hU : ∀ (φ : V) (y : G), (U φ).1 y = φ.1 (a * y)) : ‖1 - U‖ ≤ 1 / 2 := by
  refine (1 - U).opNorm_le_bound one_half_pos.le fun ⟨φ, hφ⟩ ↦ norm_le_of_nonempty.2 fun y ↦ ?_
  obtain ⟨h_fix, h_inv⟩ := (hV φ).1 hφ
  have h_rad : (y * b y * y⁻¹ * a⁻¹, 1) ∈ D := by simpa using mul_mem (hb y) (inv_mem ha)
  calc ‖((1 - U) ⟨φ, hφ⟩).1 y‖
    _ = ‖T φ y - T φ (y * b y)‖ := by
      -- `φ (a * y) = φ (y * b y)`, as `φ` is invariant under `y * b y * y⁻¹ * a⁻¹`.
      simp [hU, h_fix, ← h_inv _ h_rad (a * y), mul_assoc]
    _ ≤ 1 / 2 * ‖φ‖ := by grw [hT, hT, norm_integral_mul_translate_sub_le he φ y (b y), hb_dist y]

/-- Let `T φ y = ∫ g, e g * φ (y * g)` and `χ = exp (i H θ)`, where `|H (y * g) - H y| ≤ ℓ g` and
`|θ| * ∫ g, ‖e g‖ * ℓ g < 1`. If `T` fixes `φ` and kills `χ * φ`, then `φ = 0`. -/
lemma eq_zero_of_map_phase_mul_eq_zero {G : Type*} [Group G] [TopologicalSpace G] [MeasureSpace G]
    {e : G → ℂ} {T : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ}
    (hT : ∀ (φ : G →ᵇ ℂ) (y : G), T φ y = ∫ g : G, e g * φ (y * g)) {H ℓ : G → ℝ}
    (hℓ : Integrable fun g : G ↦ ‖e g‖ * ℓ g) (hH_lip : ∀ y g : G, |H (y * g) - H y| ≤ ℓ g) {θ : ℝ}
    (hθ : |θ| * ∫ g : G, ‖e g‖ * ℓ g < 1) {χ φ : G →ᵇ ℂ}
    (hχ : ∀ g : G, χ g = circleMap 0 1 (H g * θ)) (h_fix : T φ = φ) (h_zero : T (χ * φ) = 0) :
    φ = 0 := by
  have h_norm : ‖φ‖ ≤ |θ| * (∫ g : G, ‖e g‖ * ℓ g) * ‖φ‖ := norm_le_of_nonempty.2 fun y ↦
    calc ‖φ y‖
      _ = ‖T (χ * φ - χ y • φ) y‖ := by simp [h_zero, h_fix, hχ]
      _ = ‖∫ g : G, e g * ((χ (y * g) - χ y) * φ (y * g))‖ := by simp [hT, sub_mul, -map_sub]
      _ ≤ |θ| * (∫ g : G, ‖e g‖ * ℓ g) * ‖φ‖ := by
        simpa [hχ] using norm_integral_mul_phase_sub_le hℓ hH_lip θ φ y
  by_contra hφ
  exact (mul_lt_of_lt_one_left (norm_pos_iff.2 hφ) hθ).not_ge h_norm

/-- Let `G` be a second countable topological group with a left-invariant Borel measure. Let `e` be
integrable and `T` the operator on bounded continuous functions with `T φ y = ∫ e g * φ (y * g)`,
and let `D` be a subgroup of `G × ℂˣ`. Let `V` be the functions fixed by `T` and invariant under
left translation by every `r` with `(r, 1) ∈ D`, where `T` maps such invariant functions into `V`.
Let `H` be continuous with `|H (y * g) - H y| ≤ ℓ g`, where `‖e‖ * ℓ` is integrable, and with
`H (r * g) = H g - log ‖c‖` for `(r, c) ∈ D`. If `log ‖z‖ ≠ 0`, `(a, z) ∈ D`, and for every `y` the
element `b y` has `(y * b y * y⁻¹, z) ∈ D` and `‖e - e ((b y)⁻¹ * ·)‖` in `L¹` is less than `1 / 2`,
then `V = 0`. -/
lemma eq_zero_of_mem_fixed_invariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasureSpace G] [BorelSpace G]
    [(volume (α := G)).IsMulLeftInvariant] {e : G → ℂ}
    (he : Integrable e) {H ℓ : G → ℝ} (hℓ : Integrable fun g : G ↦ ‖e g‖ * ℓ g) (hH : Continuous H)
    (hH_lip : ∀ y g : G, |H (y * g) - H y| ≤ ℓ g) {D : Subgroup (G × ℂˣ)}
    (hD_shift : ∀ w ∈ D, ∀ g : G, H (w.1 * g) = -Real.log ‖(w.2 : ℂ)‖ + H g)
    {T : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ} (hT : ∀ (φ : G →ᵇ ℂ) (y : G), T φ y = ∫ g : G, e g * φ (y * g))
    {V : Submodule ℂ (G →ᵇ ℂ)}
    (hV : ∀ φ : G →ᵇ ℂ, φ ∈ V ↔ T φ = φ ∧ ∀ r : G, (r, 1) ∈ D → ∀ g : G, φ (r * g) = φ g)
    (hTV : ∀ φ : G →ᵇ ℂ, (∀ r : G, (r, 1) ∈ D → ∀ g : G, φ (r * g) = φ g) → T φ ∈ V)
    {a : G} {z : ℂˣ} (ha : (a, z) ∈ D) (hτ : Real.log ‖(z : ℂ)‖ ≠ 0) {b : G → G}
    (hb : ∀ y : G, (y * b y * y⁻¹, z) ∈ D)
    (hb_dist : ∀ y : G, ‖(he.sub (he.comp_mul_left (b y)⁻¹)).toL1‖ < 1 / 2) (ψ : V) : ψ = 0 := by
  -- A translation `U` close to `1` anticommutes with a power of a twisted form `S` of `T`, so `S`
  -- is nilpotent. It is also injective, so `V = 0`.
  set τ : ℝ := Real.log ‖(z : ℂ)‖
  -- `n` is so large that the phase `χ` below varies little against `e`.
  let c : ℝ := |Real.pi| / |τ| * ∫ g : G, ‖e g‖ * ℓ g
  obtain ⟨n, hn_pos, hn⟩ : ∃ n : ℕ, 0 < n ∧ c < n := by simpa using exists_nat_gt (0 ⊔ c)
  -- `U` is left translation by `a`.
  obtain ⟨U, hU⟩ := exists_left_translation_operator hT hV ha
  -- `S φ = T (χ * φ)` for the phase `χ = exp (-i π H / (τ n))`, invariant under the radical.
  let θ : ℝ := Real.pi / -τ / n
  let χ : G →ᵇ ℂ :=
    ofNormedAddCommGroup (fun g : G ↦ circleMap 0 1 (H g * θ)) (by fun_prop) 1 (by simp)
  obtain ⟨S, hS⟩ : ∃ S : V →L[ℂ] V, ∀ φ : V, (S φ).1 = T (χ * φ.1) := by
    refine ⟨(T * .mul ℂ (G →ᵇ ℂ) χ).restrict fun φ hφ ↦ hTV _ fun r hr g ↦ ?_, fun _ ↦ rfl⟩
    obtain ⟨-, h_inv⟩ := (hV φ).1 hφ
    simp [χ, hD_shift _ hr, h_inv r hr]
  -- Translation by `a` multiplies `χ` by `exp (i π / n)`, so `U` anticommutes with `S ^ n`.
  have hχ_shift (g : G) : χ (a * g) = exp (1 / n * Real.pi * I) * χ g := by
    have h_angle : H (a * g) * θ = H g * θ + 1 / n * Real.pi := by
      simp [θ, hD_shift (a, z) ha, τ, field]
    simp only [χ, coe_ofNormedAddCommGroup, circleMap, h_angle]
    simp [exp_add, mul_comm, mul_add]
  have h_semi : SemiconjBy U S (exp (1 / n * Real.pi * I) • S) := by
    ext
    simp [hU, hS, hT, ← integral_const_mul, hχ_shift, mul_left_comm, mul_assoc]
  have h_anti : U * S ^ n = -(S ^ n * U) := by
    have h_exp : exp (1 / n * Real.pi * I) ^ n = -1 := by
      simp [← exp_nat_mul, hn_pos.ne', field, mul_assoc]
    rw [(h_semi.pow_right n).eq, smul_pow, h_exp, neg_one_smul, neg_mul]
  have h_nil : S ^ n = 0 :=
    eq_zero_of_anticommute (norm_one_sub_left_translation_le he hT hV ha hb hb_dist hU) h_anti
  have h_inj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).2 fun ⟨φ, hφ⟩ hSφ ↦ Subtype.ext ?_
    have h_zero : T (χ * φ) = 0 := by simpa [hSφ] using (hS ⟨φ, hφ⟩).symm
    have hθ : |θ| * (∫ g : G, ‖e g‖ * ℓ g) = c / n := by simp [θ, c, abs_div, field]
    exact eq_zero_of_map_phase_mul_eq_zero hT hℓ hH_lip (by rwa [hθ, div_lt_one (by positivity)])
      (fun _ ↦ rfl) ((hV φ).1 hφ).1 h_zero
  exact h_inj.iterate n (by simpa using show (S ^ n) ψ = 0 by simp [h_nil])

/-- Vanishing of constant terms. Let `G` be a second countable locally compact group with left Haar
measure and let `e` be a minimal idempotent kernel (continuous, integrable, self-adjoint, with
`e * δ_x * e` a multiple of `e`) with `‖e‖ * ℓ` integrable, where `H` is a continuous function with
`|H (x * g) - H x| ≤ ℓ g`. Let `D` be a subgroup of `G × ℂˣ` such that `H (r * g) = H g - log ‖c‖`
for `(r, c) ∈ D`. Suppose that every neighbourhood `W` of `1` has a `c` with `log ‖c‖ ≠ 0` such that
for every `x` some `b ∈ W` has `(x * b * x⁻¹, c) ∈ D`. Then `∫ e g * f (x * g) = 0` for every
bounded continuous `f` with `f (r * g) = f g` whenever `(r, 1) ∈ D`.

This is meant as a step toward Harish-Chandra's theorem that `K`-finite discrete series coefficients
are cusp forms; that theorem itself is not stated here. It applies to every minimal idempotent
kernel `e` with the hypotheses on `H`, `ℓ` and `D`, and shows that `e` integrates to zero against
bounded continuous invariant functions. -/
theorem integral_idempotentKernel_mul_eq_zero {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [MeasureSpace G] [BorelSpace G]
    [(volume (α := G)).IsHaarMeasure] {e : G → ℂ} (H ℓ : G → ℝ) (D : Subgroup (G × ℂˣ))
    (h_ker : IsIdempotentKernel e) (hℓ : Integrable fun g : G ↦ ‖e g‖ * ℓ g) (hH : Continuous H)
    (hH_lip : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g)
    (hD_shift : ∀ z ∈ D, ∀ g : G, H (z.1 * g) = -Real.log ‖(z.2 : ℂ)‖ + H g)
    (hD_near : ∀ W ∈ nhds (1 : G), ∃ c : ℂˣ,
      Real.log ‖(c : ℂ)‖ ≠ 0 ∧ ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D)
    (f : G →ᵇ ℂ) (hf : ∀ r : G, (r, 1) ∈ D → ∀ g : G, f (r * g) = f g) (x : G) :
    ∫ g : G, e g * f (x * g) = 0 := by
  -- Let `T φ y = ∫ g, e g * φ (y * g)` and let `V` be the space of `φ` fixed by `T` and invariant
  -- under the radical, the `r` with `(r, 1) ∈ D`. Then `V = 0`, and `T f ∈ V`.
  have he : Integrable e := h_ker.integrable
  obtain ⟨T, hT⟩ := exists_kernel_operator he
  let V : Submodule ℂ (G →ᵇ ℂ) :=
    T.eqLocus 1 ⊓ ⨅ (r) (_ : (r, 1) ∈ D), (compContinuousCLM _ _ (.mulLeft r)).eqLocus 1
  have hV (φ : G →ᵇ ℂ) : φ ∈ V ↔ T φ = φ ∧ ∀ r : G, (r, 1) ∈ D → ∀ g : G, φ (r * g) = φ g := by
    simp [V, DFunLike.ext_iff]
  have hTV (φ : G →ᵇ ℂ) (hφ : ∀ r : G, (r, 1) ∈ D → ∀ g : G, φ (r * g) = φ g) : T φ ∈ V :=
    (hV _).2 ⟨kernel_operator_idempotent h_ker hT φ, fun r hr g ↦ by simp [hT, hφ r hr, mul_assoc]⟩
  have h_move : ContinuousAt (fun g : G ↦ DomMulAct.mk g⁻¹ • he.toL1) 1 := by fun_prop
  -- Choose a factor `z` with `log ‖z‖ ≠ 0`, and for each `y` an element `b y` with
  -- `(y * b y * y⁻¹, z) ∈ D` that moves `e` by less than `1 / 2` in `L¹`.
  obtain ⟨z, hz_log, h_conj⟩ := hD_near _ (h_move (Metric.ball_mem_nhds _ one_half_pos))
  choose b hb_move hb using h_conj
  have hb_dist (y : G) : ‖(he.sub (he.comp_mul_left (b y)⁻¹)).toL1‖ < 1 / 2 := by
    -- The action on `L¹` is translation by definition, hence `using!`.
    simpa [dist_eq_norm'] using! hb_move y
  have h_V_zero : ∀ ψ : V, ψ = 0 :=
    eq_zero_of_mem_fixed_invariant he hℓ hH hH_lip hD_shift hT hV hTV (hb 1) hz_log hb hb_dist
  have h_Tf : T f = 0 := congrArg Subtype.val (h_V_zero ⟨T f, hTV f hf⟩)
  simpa [← hT] using DFunLike.congr_fun h_Tf x

end New.DiscreteSeries

end KernelVanishing

/-! ## Dilations along an isotropic subspace meeting conjugates of balls about 1 -/

section Dilations

open Matrix Submodule New U Norms.L2Operator

/-- Every complex matrix `B` has the same kernel as some orthogonal projection, namely the
projection onto the orthogonal complement of the kernel of `B`. -/
lemma New.DiscreteSeries.exists_isStarProjection_mul_eq_zero_iff {n m : Type} [Fintype n]
    (B : Matrix m n ℂ) :
    ∃ p : Matrix n n ℂ, IsStarProjection p ∧
      ∀ {l : Type} (v : Matrix n l ℂ), p * v = 0 ↔ B * v = 0 := by
  classical
  let p : Matrix n n ℂ := (toEuclideanCLM (𝕜 := ℂ)).symm B.toEuclideanLin.kerᗮ.starProjection
  have h_vec (u : n → ℂ) : p *ᵥ u = 0 ↔ B *ᵥ u = 0 := by
    -- `starProjection_orthogonal_val` would rewrite the projection to a difference first.
    simp [← p.ofLp_toEuclideanCLM (.toLp 2 u), p, -starProjection_orthogonal_val,
      starProjection_apply_eq_zero_iff]
  refine ⟨p, .map isStarProjection_starProjection (toEuclideanCLM (𝕜 := ℂ)).symm, fun v ↦ ?_⟩
  simp_rw [Matrix.ext_col_iff]
  -- The columns of `p * v` are the images under `p` of the columns of `v`.
  exact forall_congr' fun j ↦ h_vec (v.col j)

/-- Dilations near `1`. Let `J` be a hermitian involution, let the columns of `A` be isotropic for
`J`, and let `c > 0` and `x ∈ U J`, the group of `g` with `gᴴ * J * g = J`. Then some `y ∈ U J` is
within distance `c` of `1` for the operator norm, and `x * y * x⁻¹` is a dilation along `A` by the
factor `1 + c`: this element `g` has `g * A = (1 + c) • A`, and `wᴴ * J * g * v = wᴴ * J * v`
whenever `Aᴴ * J * v = 0` and `Aᴴ * J * w = 0`. -/
theorem New.DiscreteSeries.exists_conj_mem_dilationGroup {n m : Type} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℂ} {A : Matrix n m ℂ} [hJ : IsHermitianInvolution J] (hA : Aᴴ * (J * A) = 0)
    (x : U J) {c : ℝ} (hc : 0 < c) :
    ∃ y : U J,
      dist (y : Matrix n n ℂ) 1 ≤ c ∧
      (x * y * x⁻¹, Units.mk0 (1 + c : ℂ) (mod_cast (add_pos one_pos hc).ne')) ∈
        dilationGroup A := by
  -- Let `p` be the orthogonal projection onto the span of the columns of `x⁻¹ * A`, the
  -- orthogonal complement of the kernel of `B = (x⁻¹ * A)ᴴ`, and `q = J * p * J`.
  -- The dilation is `y = 1 + c • p - (c / (1 + c)) • q`.
  let X : Matrix n n ℂ := x
  let B : Matrix m n ℂ := Aᴴ * (J * X * J)
  obtain ⟨p, hp, h_ker⟩ := exists_isStarProjection_mul_eq_zero_iff B
  let q : Matrix n n ℂ := J * p * J
  have hp_herm : pᴴ = p := hp.isSelfAdjoint
  have hJ_herm : Jᴴ = J := hJ.isHermitian
  have hJ_cancel {l : Type} (v : Matrix n l ℂ) : J * (J * v) = v := by
    simp [← J.mul_assoc, hJ.mul_self]
  have hX_adjoint : Xᴴ * J = J * X⁻¹ := by simpa using (form_mul_inv_eq x).symm
  -- `p` fixes the columns of `Bᴴ = x⁻¹ * A`.
  have h_fix : p * (X⁻¹ * A) = X⁻¹ * A := by
    have hB_adjoint : (B * (p - 1))ᴴ = 0 := by
      simp [(h_ker (p - 1)).1 (by simp [mul_sub, hp.isIdempotentElem.eq])]
    -- `↓` distributes the adjoint before the product inside it is rewritten.
    simpa [B, hJ_herm, hp_herm, Matrix.mul_assoc, hX_adjoint, hJ_cancel, Matrix.sub_mul,
      sub_eq_zero, ↓conjTranspose_mul] using hB_adjoint
  -- `p * J * x⁻¹` kills whatever is `J`-orthogonal to `A`, and likewise after taking adjoints.
  have h_kill {l : Type} (v : Matrix n l ℂ) (hv : Aᴴ * (J * v) = 0) : p * (J * (X⁻¹ * v)) = 0 := by
    simpa [h_ker, B, X, Matrix.mul_assoc, hJ_cancel] using hv
  have h_kill_adjoint {l : Type} (w : Matrix n l ℂ) (hw : Aᴴ * (J * w) = 0) (z : Matrix n n ℂ) :
      wᴴ * (J * (X * (p * z))) = 0 := by
    have hpw_adjoint : (p * (Xᴴ * J * w))ᴴ * z = 0 := by simp [hX_adjoint, J.mul_assoc, h_kill w hw]
    simpa [hJ_herm, hp_herm, Matrix.mul_assoc] using hpw_adjoint
  -- As `A` is isotropic, so is the range of `p`.
  have h_isotropic_mul (z : Matrix n n ℂ) : p * (J * (p * z)) = 0 := by
    simpa [h_ker, B, Matrix.mul_assoc, hJ_cancel] using h_kill_adjoint A hA z
  have h_isotropic : p * (J * p) = 0 := by simpa using h_isotropic_mul 1
  -- `y` preserves `J`: expand, using `p * p = p`, `J * J = 1` and `p * J * p = 0`.
  let y : Matrix n n ℂ := 1 + c • (p - (1 + c)⁻¹ • q)
  have h_expand : yᴴ * J * y =
      J + (c - c * (1 + c)⁻¹ - c * (c * (1 + c)⁻¹)) • (p * J + J * p) := by
    simp [y, q, hJ_herm, hp_herm, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, hJ_cancel,
      h_isotropic, h_isotropic_mul, hJ.mul_self, hp.isIdempotentElem.eq,
      hp.isIdempotentElem.mul_self_mul, star]
    module
  have hy : yᴴ * J * y = J := by
    simp [h_expand, show c - c * (1 + c)⁻¹ - c * (c * (1 + c)⁻¹) = 0 by field]
  refine ⟨of hJ.isUnit y hy, ?_, ?_, fun v w hv hw ↦ ?_⟩
  · -- `p` and `q` are orthogonal projections with `p * q = 0`, so `‖p - s • q‖ ≤ 1` for `|s| ≤ 1`.
    have hq : IsStarProjection q := by
      simp [q, isStarProjection_iff', star, hJ_herm, mul_assoc, hJ_cancel, hp_herm,
        hp.isIdempotentElem.mul_self_mul]
    have h_norm : ‖p - (1 + c)⁻¹ • q‖ ≤ 1 := by
      grw [hp.isSelfAdjoint.norm_sub_eq_max, norm_smul, hq.norm_le, hp.norm_le]
      · simp [abs_of_pos, inv_le_one₀, add_pos, hc, hc.le]
      · exact (IsSelfAdjoint.all (1 + c)⁻¹).smul hq.isSelfAdjoint
      · simp [q, mul_assoc, h_isotropic_mul]
    simpa [y, norm_smul, hc, abs_of_pos] using h_norm
  · -- On `x⁻¹ * A` the projection `p` is the identity and `q` vanishes.
    simp [y, q, X, Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, h_fix,
      h_kill A hA, add_smul]
  · -- Between vectors `J`-orthogonal to `A` the terms with `p` and with `q` both vanish.
    suffices wᴴ * (J * (X * y * X⁻¹ * v)) = wᴴ * (J * v) by simpa [X] using this
    simp [y, q, X, mul_assoc, add_mul, sub_mul, mul_add, mul_sub, h_kill v hv, h_kill_adjoint w hw]

end Dilations
