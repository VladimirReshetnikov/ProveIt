import Lib.Adelic.AutomorphicForms.Basic
import Lib.Adelic.QuotientMeasure.IwasawaUnfolding
import Lib.DiscreteSeries.Rigidity.KernelFixes

/-!
# Convolution over real points, cusp kernels, the Petersson product and Poincaré series

Let G = G_∞ × G_f be the adelic unitary group, and let R(α)F(g) = ∫ α(x) F(gx) dx over G_∞ be right
convolution over the real points (`New.realConv`). For integrable α, R(α) preserves bounded
automorphic functions, and convolving with an idempotent kernel e produces forms of type e. The
product of discrete series kernels over the infinite places is a cusp kernel under a gap condition.
For the Petersson product, right translation is unitary, and a cusp kernel e projects every real
translate of a form of type e to a multiple of it. A bounded Poincaré series, projected term by
term, is a form.

## Main definitions and results

* `New.continuous_realConv`, `New.Space.isAutomorphic_realConv`: for integrable α, R(α)F is
  continuous when F is bounded, measurable and has an open level, and it is automorphic and bounded
  when F is also invariant under the rational points.
* `New.Space.exists_form_eq_realConv`: convolving with an idempotent kernel gives a form of type e.
* `New.IsCuspKernel`: minimal idempotents e on G_∞ with a moment of order B + 1 and decay of order
  B, and with α ∗ e = e for some continuous compactly supported α.
* `New.isCuspKernel_typeKernel`: the product kernel `New.typeKernel` over the infinite places is
  such a kernel when the parameters satisfy a gap condition.
* `New.Space.IsForm.realConv_translate`, `New.Space.IsForm.petersson_real_translate`: `e` projects
  each real translate of a form to a multiple of the form.
* `New.Space.exists_form_eq_tsum_of_fixesLeft`: if an absolutely bounded sum of measurable functions
  is left invariant under `V.Γ` and has level `K`, projecting each term by R(e) gives a form of type
  `e`; `New.Space.exists_form_eq_tsum` is the case of a sum over `V.Γ` of translates of one
  function. `New.levelSpace (V.formRep e) K` is the space of forms of type `e` fixed by the open
  subgroup `K` of the finite points.

Notions from other files:
* `New.Space.IsAutomorphic`: continuous, left invariant under the rational points `V.Γ`, and right
  invariant under some open subgroup of G_f.
* `New.HCParam.dsKernel`: for a parameter l = 2λ, the function e_λ on U(diag s), the formal degree
  times the conjugate of the discrete series coefficient c_λ (`New.HCParam.dsCoeff`).
* `New.IsIdempotentKernel` (part of `New.IsCuspKernel`): e is continuous and integrable, e(g⁻¹) is
  the conjugate of e(g), e(1) ≠ 0, and ∫ e(z)e(x⁻¹z⁻¹y) dz = e(x⁻¹)e(y)/e(1).
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.Space.quotMeasure`: the measure on `G` that computes integrals over `Γ \ G`.

## Relation to the literature

Known result: convolution over real points, cusp kernels, the Petersson product and Poincaré series
projected to forms, from the theory of cusp forms. For sources see
`Lib.Adelic.AutomorphicForms.Cuspidality`.
-/

/-! ## Convolution over the real points; cusp kernels -/

section RealConvolution

open MeasureTheory Finset Matrix.Norms.L2Operator CompactlySupported Asymptotics

namespace New

variable {E n : Type _} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {F : G E s → ℂ} {α : GInf E s → ℂ}

/-- For a bump function α_w on U(diag s) at each infinite place w, the product x ↦ ∏_w α_w(x_w⁻¹),
as a continuous compactly supported function on G_∞. -/
noncomputable def bumpProduct (α : NumberField.InfinitePlace E → DiscreteSeries.Bumps s) :
    C_c(GInf E s, ℂ) where
  toFun x := ∏ w : NumberField.InfinitePlace E, (α w).val.val (x w)⁻¹
  continuous_toFun := by fun_prop
  hasCompactSupport' := HasCompactSupport.intro (isCompact_univ_pi fun w ↦ (α w).2.inv) (by
    grind [prod_eq_zero_iff, image_eq_zero_of_notMem_tsupport, Set.mem_inv])

/-- For `n` nonempty and `g` in G_∞, the product over the infinite places of the operator norms
‖g_w‖ is at least 1 and at least each of its factors. -/
theorem le_prod_opNorm [Nonempty n] (g : GInf E s) :
    1 ≤ ∏ w : NumberField.InfinitePlace E, ‖(g w).val.val‖ ∧
    ∀ w : NumberField.InfinitePlace E,
      ‖(g w).val.val‖ ≤ ∏ v : NumberField.InfinitePlace E, ‖(g v).val.val‖ := by
  have h_one (v : NumberField.InfinitePlace E) : 1 ≤ ‖(g v).val.val‖ := U.one_le_norm (g v)
  refine ⟨one_le_prod₀ fun v _ ↦ h_one v, fun w ↦ ?_⟩
  rw [← mul_prod_erase univ _ (mem_univ w)]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_prod₀ fun v _ ↦ h_one v)

/-- A cusp kernel of order B on G_∞: a minimal idempotent e (`New.IsIdempotentKernel`) such that,
with ‖x‖ = ∏_w ‖x_w‖ for the operator norms, (a) ‖x‖^(B+1) e(x) is integrable, (b) α ∗ e = e for
some continuous compactly supported α, and (c) ‖x‖^B e(x) is bounded. -/
structure IsCuspKernel (B : ℕ) (e : GInf E s → ℂ) extends IsIdempotentKernel e where
  /-- Moment: |e(x)| ‖x‖ ^ (B + 1) is integrable, where ‖x‖ is the product over the infinite places
  of the operator norms. -/
  integrable_moment :
      Integrable fun x : GInf E s ↦
        ‖e x‖ * (∏ w : NumberField.InfinitePlace E, ‖(x w).val.val‖) ^ (B + 1)
  /-- Some continuous compactly supported `α` reproduces `e` by convolution: α ∗ e = e. -/
  exists_bump : ∃ α : GInf E s →C_c ℂ, ∀ y : GInf E s, ∫ x : GInf E s, α x * e (x⁻¹ * y) = e y
  /-- Decay of order `B`: |e(x)| ‖x‖ ^ B is bounded. -/
  decay : ∃ C : ℝ, ∀ x : GInf E s,
    ‖e x‖ * (∏ w : NumberField.InfinitePlace E, ‖(x w).val.val‖) ^ B ≤ C

/-- The complex conjugate of a cusp kernel of order `B` is a cusp kernel of order `B`. -/
theorem IsCuspKernel.star {B : ℕ} {e : GInf E s → ℂ} (he : IsCuspKernel B e) :
    IsCuspKernel B (star e) where
  continuous := he.continuous.star
  integrable := (starL' ℝ).integrable_comp_iff.2 he.integrable
  apply_inv g := by simp [he.apply_inv]
  apply_one_ne_zero := by simpa using he.apply_one_ne_zero
  convolution_eq x y := by
    simpa [← integral_conj] using congrArg (starRingEnd ℂ) (he.convolution_eq x y)
  integrable_moment := by simpa using he.integrable_moment
  exists_bump := he.exists_bump.elim fun α hα ↦
    -- Conjugate the equation `α ∗ e = e`.
    ⟨Star.star α, fun y ↦ by simpa [← integral_conj] using congrArg (starRingEnd ℂ) (hα y)⟩
  decay := by simpa using he.decay

/-- For n nonempty, suppose that at every infinite place w the integer vector l_w = 2λ_w, read by
`toHCParam` as a doubled parameter for the signs s, is a parameter with gap 500|n|³ + B
(`HasLargeGap B`). Then `New.typeKernel` l s, the product over the infinite places of the discrete
series kernels e_(l_w), is an idempotent kernel on G_∞. That is, it is continuous and integrable,
e(g⁻¹) = conj(e(g)), e(1) ≠ 0, and ∫ e(z) e(x⁻¹z⁻¹y) dz = e(x⁻¹) e(y) / e(1). -/
theorem isIdempotentKernel_typeKernel [Nonempty n] {l : NumberField.InfinitePlace E → n → ℤ}
    {B : ℕ} (h : ∀ w : NumberField.InfinitePlace E, (toHCParam s (l w)).HasLargeGap B) :
    IsIdempotentKernel (typeKernel (E := E) l s) := by
  -- Every property is the product over the infinite places of the property of `HCParam.dsKernel`.
  have h_loc (w : NumberField.InfinitePlace E) :
      IsIdempotentKernel (toHCParam s (l w)).dsKernel := (h w).isIdempotentKernel_dsKernel
  exact
    { continuous := by fun_prop
      integrable := .fintype_prod fun w ↦ (h_loc w).integrable
      apply_inv := by simp [typeKernel, ← (h_loc _).apply_inv]
      apply_one_ne_zero := by simp [typeKernel, (h_loc _).apply_one_ne_zero, prod_eq_zero_iff]
      convolution_eq := by simp [typeKernel, mul_assoc, ← prod_mul_distrib, ← prod_div_distrib,
        ← integral_fintype_prod_volume_eq_prod, ← (h_loc _).convolution_eq] }

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let E be a CM field, n nonempty and s a family of signs. Suppose every l_w = 2λ_w is a
Harish-Chandra parameter whose entries λ_i, λ_j of different signs s are at least 500|n|³ + B apart.
Then `New.typeKernel` l s, the product over the infinite places of the discrete series kernels
e_(l_w), is a cusp kernel of order B: a minimal idempotent e on G_∞ such that, with ‖x‖ = ∏_w ‖x_w‖
the product of operator norms, ‖x‖^(B+1) e(x) is integrable, α ∗ e = e for some continuous compactly
supported α, and ‖x‖^B e(x) is bounded. -/
theorem isCuspKernel_typeKernel [Nonempty n] {l : NumberField.InfinitePlace E → n → ℤ} {B : ℕ}
    (h : ∀ w : NumberField.InfinitePlace E, (toHCParam s (l w)).HasLargeGap B) :
    IsCuspKernel B (typeKernel (E := E) l s) := by
  -- The moment, the bump function and the decay bound are products of the local ones.
  let e (w : NumberField.InfinitePlace E) : USign s → ℂ := (toHCParam s (l w)).dsKernel
  have h_prod (x : GInf E s) : typeKernel l s x = ∏ w, e w (x w) := rfl
  have h_moment : Integrable fun x : GInf E s ↦
      ‖typeKernel l s x‖ * (∏ w, ‖(x w).val.val‖) ^ (B + 1) := by
    have h_loc : Integrable fun x : GInf E s ↦
        ∏ w, e w (x w) * (‖(x w).val.val‖ : ℂ) ^ (B + 1) :=
      .fintype_prod fun w ↦ (h w).integrable_dsKernel_mul_norm_pow (B + 1) le_rfl
    simpa [h_prod, prod_mul_distrib, prod_pow] using h_loc.norm
  have h_bump (w : NumberField.InfinitePlace E) : ∃ α : DiscreteSeries.Bumps s,
      ∀ g : USign s, ∫ x : USign s, α.val.val x⁻¹ * e w (x⁻¹ * g) = e w g :=
    (h w).exists_bump_conv_dsKernel
  choose α hα using h_bump
  have h_fix (y : GInf E s) :
      ∫ x : GInf E s, bumpProduct α x * typeKernel l s (x⁻¹ * y) = typeKernel l s y :=
    calc
      _ = ∫ x : GInf E s, ∏ w, (α w).val.val (x w)⁻¹ * e w ((x w)⁻¹ * y w) := by
        simp [h_prod, bumpProduct, prod_mul_distrib]
      _ = ∏ w, ∫ x : USign s, (α w).val.val x⁻¹ * e w (x⁻¹ * y w) :=
        integral_fintype_prod_volume_eq_prod fun w x ↦ (α w).val.val x⁻¹ * e w (x⁻¹ * y w)
      _ = typeKernel l s y := by simp only [hα, h_prod]
  -- `e w` is the formal degree times the conjugate of the coefficient c, and |c(g)| ≤ (2 / ‖g‖)^B.
  have h_place (w : NumberField.InfinitePlace E) (g : USign s) :
      ‖e w g‖ * ‖g.val.val‖ ^ B ≤ ‖(toHCParam s (l w)).formalDegree‖ * 2 ^ B := by
    have h_pos : 0 < ‖g.val.val‖ := one_pos.trans_le (U.one_le_norm g)
    have h_coeff : ‖(toHCParam s (l w)).dsCoeff g‖ * ‖g.val.val‖ ^ B ≤ 2 ^ B := by
      rw [← le_div_iff₀ (pow_pos h_pos B), ← div_pow]
      exact DiscreteSeries.norm_dsCoeff_le_pow (h w) (by simp) g
    simpa [e, HCParam.dsKernel, mul_assoc] using
      mul_le_mul_of_nonneg_left h_coeff (norm_nonneg (toHCParam s (l w)).formalDegree)
  refine ⟨isIdempotentKernel_typeKernel h, h_moment, ⟨bumpProduct α, h_fix⟩,
    ∏ w, ‖(toHCParam s (l w)).formalDegree‖ * 2 ^ B, fun g ↦ ?_⟩
  rw [h_prod, norm_prod, ← prod_pow, ← prod_mul_distrib]
  exact prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦ h_place w (g w)

@[simp]
theorem Space.formRep_apply (k : Gf E n) (y : V.Form α) (g : G E s) :
    V.formRep α k y g = y (g * (1, k)) :=
  rfl

/-- A form of type `α` (a bounded automorphic function fixed by `realConv α` when α is integrable)
lies in `levelSpace (V.formRep α) J`, the vectors fixed by the subgroup `J` of G_f, if and only if
it has level `J`, that is, is invariant under right translation by `J`. -/
lemma Space.mem_levelSpace_formRep_iff {J : Subgroup (Gf E n)} {y : V.Form α} :
    y ∈ levelSpace (V.formRep α) J ↔ HasLevel y J := by
  have h_fix (k : Gf E n) : V.formRep α k y = y ↔ ∀ g : G E s, y (g * (1, k)) = y g :=
    Subtype.ext_iff.trans funext_iff
  simp [h_fix]

/-- If `F` is right invariant under the open subgroup `K` of G_f, then so is its real convolution
R(α)F, since real and finite points commute. -/
lemma hasLevel_realConv (K : OpenSubgroup (Gf E n)) (h_level : HasLevel F K) :
    HasLevel (realConv α F) K := by
  intro k hk g
  have h_comm (x : GInf E s) : g * (1, k) * (x, 1) = g * (x, 1) * (1, k) := by simp [Prod.ext_iff]
  simp only [realConv, h_comm, h_level k hk]

/-- The oscillation of an average is bounded by that of the kernel in L¹. Let α be integrable on
G_∞, F bounded and measurable on G, u a real point, real points sitting in G as x ↦ (x, 1), and
R(α)F(g) = ∫_{G_∞} α(x)F(gx) dx (`realConv`). If C ≥ 0 and |F(gx)| ≤ C for all real x with
α(u⁻¹x) ≠ α(x), then |R(α)F(gu) − R(α)F(g)| ≤ ‖α(u⁻¹ ·) − α‖₁ C. -/
lemma norm_realConv_mul_sub_le (hF : IsBoundedMeasurable F) (hα : Integrable α) (g : G E s)
    (u : GInf E s) {C : ℝ} (_hC_nonneg : 0 ≤ C)
    (hC : ∀ x : GInf E s, α (u⁻¹ * x) ≠ α x → ‖F (g * (x, 1))‖ ≤ C) :
    ‖realConv α F (g * (u, 1)) - realConv α F g‖ ≤
      (∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) * C := by
  -- The difference of the averages is ∫ (α(u⁻¹x) - α(x)) F(gx) dx.
  have h_int {β : GInf E s → ℂ} (hβ : Integrable β) :
      Integrable fun x : GInf E s ↦ β x * F (g * (x, 1)) :=
    hF.integrable_mul_comp hβ (fun x : GInf E s ↦ g * (x, 1)) (by fun_prop)
  have h_shift : realConv α F (g * (u, 1)) = ∫ x, α (u⁻¹ * x) * F (g * (x, 1)) := by
    rw [← integral_mul_left_eq_self (fun x : GInf E s ↦ α (u⁻¹ * x) * F (g * (x, 1))) u]
    simp [realConv, mul_assoc]
  have h_eq : realConv α F (g * (u, 1)) - realConv α F g =
      ∫ x, (α (u⁻¹ * x) - α x) * F (g * (x, 1)) := by
    rw [h_shift, realConv, ← integral_sub (h_int (hα.comp_mul_left u⁻¹)) (h_int hα)]
    simp only [sub_mul]
  -- Where the first factor does not vanish, the second has norm at most `C`.
  have h_le (x : GInf E s) :
      ‖(α (u⁻¹ * x) - α x) * F (g * (x, 1))‖ ≤ ‖α (u⁻¹ * x) - α x‖ * C := by
    by_cases hx : α (u⁻¹ * x) = α x
    · simp [hx]
    · exact norm_mul_le_of_le le_rfl (hC x hx)
  rw [h_eq, ← integral_mul_const]
  exact norm_integral_le_of_norm_le (((hα.comp_mul_left u⁻¹).sub hα).norm.mul_const C)
    (.of_forall h_le)

/-- Translation is continuous on L¹: for α integrable on G_∞, ‖α(u⁻¹ ·) − α‖₁ tends to 0 as the
real point u tends to 1. -/
lemma tendsto_integral_norm_translate_sub (hα : Integrable α) :
    Filter.Tendsto (fun u : GInf E s ↦ ∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) (nhds 1) (nhds 0) := by
  have : SMulInvariantMeasure (GInf E s) (GInf E s) volume :=
    Measure.IsMulLeftInvariant.smulInvariantMeasure
  let T (u : GInf E s) : Lp ℂ 1 (volume : Measure (GInf E s)) := DomMulAct.mk u⁻¹ • hα.toL1
  have h_cont : Continuous T :=
    -- `continuous_smul` for the action on L¹, whose instance is not found by unification here
    Lp.instContinuousSMulDomMulAct.1.comp
      (f := fun u : GInf E s ↦ (DomMulAct.mk u⁻¹, hα.toL1)) (by fun_prop)
  have h_norm (u : GInf E s) : ‖T u - T 1‖ = ∫ x : GInf E s, ‖α (u⁻¹ * x) - α (1⁻¹ * x)‖ :=
    L1.norm_of_fun_eq_integral_norm ((hα.comp_mul_left u⁻¹).sub (hα.comp_mul_left 1⁻¹))
  simpa only [h_norm, inv_one, one_mul] using tendsto_iff_norm_sub_tendsto_zero.1 (h_cont.tendsto 1)

/-- Uniform continuity of averages. Let α be integrable on G_∞, K an open subgroup of G_f and ε > 0.
Let z be close enough to 1, with real part z_∞. If (a) F is measurable, bounded and right
K-invariant and (b) |F(gx)| ≤ C for all real x with α(z_∞⁻¹x) ≠ α(x), then
|R(α)F(gz) − R(α)F(g)| ≤ ε|C|. The neighbourhood of 1 does not depend on F, C or g. -/
lemma eventually_norm_realConv_sub_le (K : OpenSubgroup (Gf E n)) (hα : Integrable α) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ z : G E s in nhds 1, ∀ {F : G E s → ℂ} (C : ℝ), IsBoundedMeasurable F → HasLevel F K →
      ∀ g : G E s,
      (∀ x : GInf E s, α (z.1⁻¹ * x) ≠ α x → ‖F (g * (x, 1))‖ ≤ C) →
      ‖realConv α F (g * z) - realConv α F g‖ ≤ ε * ‖C‖ := by
  -- Near 1 the finite part a of z lies in K and drops out, and the real part u moves α by less
  -- than ε in L¹.
  have h_L1 : ∀ᶠ u : GInf E s in nhds 1, ∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖ < ε :=
    (tendsto_integral_norm_translate_sub hα).eventually_lt_const hε
  filter_upwards [continuousAt_snd K.mem_nhds_one, continuousAt_fst h_L1]
    with ⟨u, a⟩ ha hu F C hF h_level g hC
  have h_split : g * (u, a) = g * (u, 1) * (1, a) := by simp [mul_assoc]
  calc ‖realConv α F (g * (u, a)) - realConv α F g‖
      = ‖realConv α F (g * (u, 1)) - realConv α F g‖ := by
        rw [h_split, hasLevel_realConv K h_level a ha]
    _ ≤ (∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) * ‖C‖ :=
        norm_realConv_mul_sub_le hF hα g u (norm_nonneg C) fun x hx ↦
          (hC x hx).trans C.le_norm_self
    _ ≤ ε * ‖C‖ := mul_le_mul_of_nonneg_right (le_of_lt hu) (norm_nonneg C)

/-- Fubini for right convolution: for c, α integrable, j measurable and F bounded measurable on
G, ∫ c(z) R(α)F(j z) dν(z) = ∫_{G_∞} α(x) ∫ c(z) F(j(z)x) dν(z) dx, with ν s-finite. -/
lemma integral_mul_realConv (hF : IsBoundedMeasurable F) (hα : Integrable α) {Z : Type*}
    [MeasurableSpace Z] {ν : Measure Z} [SFinite ν] {c : Z → ℂ} (hc : Integrable c ν)
    (j : Z → G E s) (hj : Measurable j := by fun_prop) :
    ∫ z : Z, c z * realConv α F (j z) ∂ν =
      ∫ x : GInf E s, α x * ∫ z : Z, c z * F (j z * (x, 1)) ∂ν := by
  -- The integrand `c z * α x * F (j z * (x, 1))` is an integrable product times a bounded
  -- measurable function.
  simp_rw [realConv, ← integral_const_mul, ← mul_assoc, mul_comm (α _)]
  exact integral_integral_swap (hF.integrable_mul_comp (hc.mul_prod hα) _ (by fun_prop))

/-- Averaging twice is averaging against a convolution: for F measurable and bounded, α and p
integrable and a in G_∞, applying R(p), then right translation by a, then R(α) is R of the function
y ↦ ∫ α(x) p((xa)⁻¹y) dx. Here R = `realConv` is right convolution over G_∞. -/
theorem realConv_realConv (hF : IsBoundedMeasurable F) (hα : Integrable α) {p : GInf E s → ℂ}
    (hp : Integrable p) (a : GInf E s) :
    realConv α (fun g : G E s ↦ realConv p F (g * (a, 1))) =
      realConv (fun y : GInf E s ↦ ∫ x : GInf E s, α x * p ((x * a)⁻¹ * y)) F := by
  ext ⟨g, k⟩
  -- Fubini's theorem and a left translation of the inner variable by `x * a`.
  have h_meas : Measurable fun x : GInf E s ↦ ((g * x, k) : G E s) := by fun_prop
  have h_conv : ∫ x, α x * ∫ y, p y * F (g * (x * a * y), k) =
      ∫ y, (∫ x, α x * p ((x * a)⁻¹ * y)) * F (g * y, k) :=
    integral_smul_integral_eq_integral_conv_smul (fun x : GInf E s ↦ x * a) hα hp
      (hF.comp h_meas) (by fun_prop)
  simpa [realConv, mul_assoc, Prod.mul_def] using h_conv

/-- For a cusp kernel e (an integrable idempotent kernel on G_∞ with decay, `IsCuspKernel`) there is
a continuous compactly supported α on G_∞ with α ∗ e = e, and so R(α)R(e)F = R(e)F for every bounded
measurable F on G. Here R(α)F(g) = ∫_{G_∞} α(x) F(gx) dx is `realConv`. -/
theorem IsCuspKernel.exists_realConv_realConv_eq {B : ℕ} {e : GInf E s → ℂ}
    (he : IsCuspKernel B e) :
    ∃ α : GInf E s →C_c ℂ,
      (∀ y : GInf E s, ∫ x : GInf E s, α x * e (x⁻¹ * y) = e y) ∧
      ∀ F : G E s → ℂ, IsBoundedMeasurable F → realConv α (realConv e F) = realConv e F := by
  obtain ⟨α, hα⟩ := he.exists_bump
  refine ⟨α, hα, fun F hF ↦ ?_⟩
  simpa [hα, Prod.mk_one_one] using realConv_realConv hF α.integrable he.integrable 1

/-- Rank one formula for operators. Let α be an idempotent kernel on G_∞ (continuous, integrable,
α(g⁻¹) = conj(α(g)), α(1) ≠ 0, and ∫ α(z) α(x⁻¹z⁻¹y) dz = α(x⁻¹) α(y) / α(1)), x a real point, and F
on G bounded and measurable. Then applying R(α)F(g) = ∫_{G_∞} α(z) F(gz) dz, then right translation
by (x, 1), then R(α) again gives conj(α(x))/α(1) times R(α)F. For the kernel e_λ of a discrete
series the factor is the coefficient c_λ(x). -/
theorem IsIdempotentKernel.realConv_translate_realConv (hα : IsIdempotentKernel α)
    (hF : IsBoundedMeasurable F) (x : GInf E s) (g : G E s) :
    realConv α (fun g' : G E s ↦ realConv α F (g' * (x, 1))) g =
      starRingEnd ℂ (α x) / α 1 * realConv α F g := by
  -- The two averages combine into one, against a function that `hα.convolution_eq` computes.
  calc
    _ = realConv (fun y : GInf E s ↦ ∫ z : GInf E s, α z * α ((z * x)⁻¹ * y)) F g :=
      congrFun (realConv_realConv hF hα.integrable hα.integrable x) g
    _ = realConv (fun y : GInf E s ↦ α x⁻¹ / α 1 * α y) F g := by simp only [hα.convolution_eq]
    _ = α x⁻¹ / α 1 * realConv α F g := by simp [realConv, ← integral_const_mul, mul_assoc]
    _ = starRingEnd ℂ (α x) / α 1 * realConv α F g := by rw [hα.apply_inv]

/-- For bounded measurable `F`, `F'` and integrable `α`, the convolution in the right argument may
be taken out of the Petersson product `V.petersson`, the integral of `conj F' * F` over `Γ \ G`. -/
theorem Space.petersson_realConv_right (hF : IsBoundedMeasurable F) (hα : Integrable α)
    {F' : G E s → ℂ} (hF' : IsBoundedMeasurable F') :
    V.petersson F' (realConv α F) =
      ∫ x : GInf E s, α x * V.petersson F' fun g : G E s ↦ F (g * (x, 1)) := by
  have hF'_int : Integrable (star F') V.quotMeasure := hF'.memLp_top.star.integrable le_top
  simpa [petersson] using integral_mul_realConv hF hα hF'_int id measurable_id

/-- If F on G is measurable, bounded and right invariant under an open subgroup of G_f, and α is
integrable on G_∞, then R(α)F is continuous. -/
theorem continuous_realConv (K : OpenSubgroup (Gf E n)) (hF : IsBoundedMeasurable F)
    (h_level : HasLevel F K) (hα : Integrable α) : Continuous (realConv α F) := by
  obtain ⟨C, hC⟩ := hF.bounded
  -- At `g`, the difference `R(α)F(gz) - R(α)F(g)` is `o(C)` as `z → 1`.
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  have h_small : (fun z : G E s ↦ realConv α F (g * z) - realConv α F g) =o[nhds 1]
      fun _ : G E s ↦ C := by
    refine .of_bound fun ε hε ↦ ?_
    filter_upwards [eventually_norm_realConv_sub_le K hα hε] with z hz
    exact hz C hF h_level g fun x _ ↦ hC (g * (x, 1))
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, ← map_mul_left_nhds_one g]
  exact Filter.tendsto_map' (h_small.tendsto_zero_of_tendsto tendsto_const_nhds)

/-- If F on G is measurable, bounded, left Γ-invariant and right invariant under an open
subgroup of G_f, and α is integrable on G_∞, then R(α)F is automorphic (continuous,
Γ-invariant, with a level) and bounded. -/
theorem Space.isAutomorphic_realConv (K : OpenSubgroup (Gf E n)) (hF : IsBoundedMeasurable F)
    (hF_rat : V.Γ.FixesLeft F) (hF_level : HasLevel F K) (hα : Integrable α) :
    V.IsAutomorphic (realConv α F) ∧ IsBoundedMeasurable (realConv α F) := by
  obtain ⟨C, hC⟩ := hF.bounded
  -- The bound is `C` times the L¹ norm of `α`; the invariances pass under the integral.
  have h_bound (g : G E s) : ‖realConv α F g‖ ≤ ∫ x, ‖α x‖ * C :=
    norm_integral_le_of_norm_le (hα.norm.mul_const C) (by simp [mul_le_mul, hC])
  have h_rat : V.Γ.FixesLeft (realConv α F) := fun γ hγ g ↦ by
    simp only [realConv, mul_assoc γ, hF_rat γ hγ]
  have h_cont : Continuous (realConv α F) := continuous_realConv K hF hF_level hα
  exact ⟨⟨h_cont, h_rat, K, hasLevel_realConv K hF_level⟩, .of_continuous ⟨_, h_bound⟩ h_cont⟩

/-- Let α be an idempotent kernel on G_∞ (`New.IsIdempotentKernel`: continuous, integrable,
α(g⁻¹) = conj(α(g)), α(1) ≠ 0, and ∫ α(z) α(x⁻¹z⁻¹y) dz = α(x⁻¹) α(y) / α(1)). Let K be an open
subgroup of G_f, and F on G bounded, measurable, left invariant under the subgroup `V.Γ` and right
invariant under K. Then R(α)F(g) = ∫_{G_∞} α(x) F(gx) dx is a form of type α (automorphic, bounded
and fixed by R(α)) fixed by right translation by K, that is an element of
`New.levelSpace (V.formRep α) K`. -/
theorem Space.exists_form_eq_realConv (K : OpenSubgroup (Gf E n)) (hF : IsBoundedMeasurable F)
    (hF_rat : V.Γ.FixesLeft F) (hF_level : HasLevel F K) (hα : IsIdempotentKernel α) :
    ∃ y : levelSpace (V.formRep α) K.toSubgroup, (y.val : G E s → ℂ) = realConv α F := by
  obtain ⟨h_aut, h_bdd⟩ := isAutomorphic_realConv K hF hF_rat hF_level hα.integrable
  -- R(α) fixes R(α)F because α * α = α.
  have h_fix : realConv α (realConv α F) = realConv α F := by
    simpa [Prod.mul_def, hα.convolution_self] using
      realConv_realConv hF hα.integrable hα.integrable 1
  exact ⟨⟨⟨realConv α F, h_aut, h_bdd.bounded, fun _ ↦ h_fix⟩,
    mem_levelSpace_formRep_iff.2 (hasLevel_realConv K hF_level)⟩, rfl⟩

end New

end RealConvolution

/-!
## The Petersson product under translation and convolution

The product `New.Space.petersson F F'` is the integral of `conj F * F'` over `Γ \ G`. A form of type
`e` (`New.Space.IsForm`) is a bounded automorphic function fixed by `realConv e` when `e` is
integrable.

In `New.Space.IsForm.realConv_translate`, `New.Space.IsForm.petersson_real_translate` and
`New.Space.IsForm.petersson_realConv_realConv`, `e` is taken to be a cusp kernel
(`New.IsCuspKernel`), though of its properties only those of an idempotent kernel are used.
-/

section Petersson

open MeasureTheory ComplexConjugate InnerProductSpace

namespace New.Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {e : GInf E s → ℂ} {F F' : G E s → ℂ} {B : ℕ}

/-! ### Translation -/

/-- For a continuous left `V.Γ`-invariant function F on G and x in G, the right translate
g ↦ F(gx) has the same integral over `Γ \ G` as F, and it is integrable if and only if F is. -/
lemma integral_comp_mul_right (x : G E s) (h_rat : V.Γ.FixesLeft F)
    (hF : Continuous F := by fun_prop) :
    ∫ g : G E s, F (g * x) ∂V.quotMeasure = ∫ g : G E s, F g ∂V.quotMeasure ∧
    (Integrable (fun g : G E s ↦ F (g * x)) V.quotMeasure ↔ Integrable F V.quotMeasure) := by
  have h : ProbabilityTheory.IdentDistrib (fun g ↦ F (g * x)) F V.quotMeasure V.quotMeasure :=
    identDistrib_orbitMeasure_mul_right x fun γ ↦ h_rat γ γ.property
  exact ⟨h.integral_eq, h.integrable_iff⟩

theorem inner_eq_petersson (y y' : V.Form e) : ⟪y, y'⟫_ℂ = V.petersson y y' := rfl

/-- For automorphic functions `F`, `F'` and the Petersson product, right translation by `x⁻¹` is
adjoint to right translation by `x`. -/
lemma IsAutomorphic.petersson_comp_mul_right (hF : V.IsAutomorphic F) (hF' : V.IsAutomorphic F')
    (x : G E s) :
    V.petersson (fun g : G E s ↦ F (g * x)) F' = V.petersson F (fun g : G E s ↦ F' (g * x⁻¹)) := by
  have h_inv : V.Γ.FixesLeft fun g : G E s ↦ conj (F g) * F' (g * x⁻¹) := fun γ hγ g ↦ by
    simp [mul_assoc γ, hF.rat_mul γ hγ, hF'.rat_mul γ hγ]
  have := hF.continuous
  have := hF'.continuous
  -- Translate the integrand `conj (F g) * F' (g * x⁻¹)` by `x`.
  simpa [petersson] using (integral_comp_mul_right x h_inv).1

/-- The finite points act on forms of type `e` by isometries of the Petersson product. -/
theorem inner_formRep (k : Gf E n) (y y' : V.Form e) :
    ⟪V.formRep e k y, V.formRep e k y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
  -- Move the translation by `(1, k)` from the left factor to the right one, where it cancels.
  change V.petersson (fun g ↦ y (g * (1, k))) (fun g ↦ y' (g * (1, k))) = V.petersson y y'
  simpa [-Prod.inv_mk] using
    y.prop.petersson_comp_mul_right (y'.prop.comp_mul_right k).toIsAutomorphic (1, k)

@[simp]
theorem conj_petersson : conj (V.petersson F F') = V.petersson F' F := by
  simp [petersson, mul_comm, ← integral_conj]

/-! ### Forms of type `e` -/

/-- Right convolution with an idempotent kernel `e` is self-adjoint for the Petersson product on
bounded automorphic functions, because `e y⁻¹ = conj (e y)`. -/
theorem petersson_realConv_comm (he : IsIdempotentKernel e) (hF_aut : V.IsAutomorphic F)
    (hF_bdd : IsBoundedMeasurable F) (hF'_aut : V.IsAutomorphic F')
    (hF'_bdd : IsBoundedMeasurable F') :
    V.petersson F (realConv e F') = V.petersson (realConv e F) F' := by
  -- Move the translation by `y` across the product, use `e y⁻¹ = conj (e y)`, and invert the
  -- variable.
  calc
    _ = ∫ y : GInf E s, e y * V.petersson F fun g : G E s ↦ F' (g * (y, 1)) :=
      petersson_realConv_right hF'_bdd he.integrable hF_bdd
    _ = ∫ y : GInf E s, e y * V.petersson (fun g : G E s ↦ F (g * (y⁻¹, 1))) F' := by
      simp [hF_aut.petersson_comp_mul_right hF'_aut]
    _ = conj (∫ y : GInf E s, e y⁻¹ * V.petersson F' fun g : G E s ↦ F (g * (y⁻¹, 1))) := by
      simp [he.apply_inv, ← integral_conj]
    _ = conj (∫ y : GInf E s, e y * V.petersson F' fun g : G E s ↦ F (g * (y, 1))) := by
      rw [integral_inv_eq_self (fun y ↦ e y * V.petersson F' fun g ↦ F (g * (y, 1))) volume]
    _ = V.petersson (realConv e F) F' := by
      rw [← petersson_realConv_right hF_bdd he.integrable hF'_bdd, conj_petersson]

/-- Let `e` be an idempotent kernel, `F` a form of type `e` and `T` a bounded automorphic function.
Replacing `T` by its right convolution `realConv e T` does not change the Petersson product of `F`
and `T`: convolution by `e` is self-adjoint and fixes `F`. -/
theorem IsForm.petersson_realConv (he : IsIdempotentKernel e) (hF : V.IsForm e F) {T : G E s → ℂ}
    (hT_aut : V.IsAutomorphic T) (hT_bdd : IsBoundedMeasurable T) :
    V.petersson F (realConv e T) = V.petersson F T := by
  rw [petersson_realConv_comm he hF.toIsAutomorphic hF.isBoundedMeasurable hT_aut hT_bdd,
    hF.realConv_eq he.integrable]

/-- For a hermitian space `V` over the CM field `E` with signs `s`, let `F` be a function on the
unitary group `G E s` that is a form of type `e`, where `e` is a function on the archimedean group
`GInf E s`. Being a form of type `e` means `F` is automorphic, bounded, and fixed by right
convolution with `e` when `e` is integrable. Then the complex conjugate `star F` is a form of type
`star e`. -/
theorem IsForm.conj (h : V.IsForm e F) : V.IsForm (star e) (star F) := by
  refine ⟨h.toIsAutomorphic.conj, h.bounded.imp (by simp), fun h_int ↦ funext fun g ↦ ?_⟩
  have h_fix : realConv e F = F := h.realConv_eq ((starL' ℝ).integrable_comp_iff.1 h_int)
  simpa [realConv, ← integral_conj] using congrArg (starRingEnd ℂ) (congrFun h_fix g)

/-- Rank one formula. Let `e` be a cusp kernel (a minimal idempotent on G_∞ with the decay
conditions of `IsCuspKernel`), `F` a form of type `e` (bounded automorphic on G, fixed by right
convolution with `e`), and `x` a real point. Convolution by `e` sends the translate `F (· * (x, 1))`
to `conj (e x) / e 1` times `F`. The left side is the value at `g` of `realConv e` applied to that
translate. For the kernel e_λ of a discrete series the factor is the coefficient c_λ(x). -/
theorem IsForm.realConv_translate (he : IsCuspKernel B e) (h : V.IsForm e F) (x : GInf E s)
    (g : G E s) :
    ∫ z : GInf E s, e z * F (g * (z, 1) * (x, 1)) = conj (e x) / e 1 * F g := by
  have h_fix : realConv e F = F := h.realConv_eq he.integrable
  calc
    _ = realConv e (fun g' : G E s ↦ realConv e F (g' * (x, 1))) g := by rw [h_fix, realConv]
    _ = conj (e x) / e 1 * F g := by
      rw [he.toIsIdempotentKernel.realConv_translate_realConv h.isBoundedMeasurable x g, h_fix]

/-- For a cusp kernel `e`, forms `F`, `F'` of type `e` and a real point `x`, the Petersson product
of `F` with the translate `F' (· * (x, 1))` is `conj (e x) / e 1` times the product of `F` and
`F'`. -/
theorem IsForm.petersson_real_translate (he : IsCuspKernel B e) (h : V.IsForm e F)
    (h' : V.IsForm e F') (x : GInf E s) :
    V.petersson F (fun g : G E s ↦ F' (g * (x, 1))) = conj (e x) / e 1 * V.petersson F F' := by
  have rank_one : realConv e (fun g : G E s ↦ F' (g * (x, 1))) =
      fun g : G E s ↦ conj (e x) / e 1 * F' g :=
    funext (h'.realConv_translate he x)
  -- Convolve the translate of `F'` with `e`, which does not change its product with `F`, and apply
  -- the rank one formula.
  rw [← h.petersson_realConv he.toIsIdempotentKernel (h'.toIsAutomorphic.comp_mul_right (x, 1))
    (h'.isBoundedMeasurable.comp (measurable_mul_const (x, 1))), rank_one]
  simp [petersson, mul_left_comm, ← integral_const_mul]

/-- For a cusp kernel `e`, forms `F`, `F'` of type `e` and integrable `α`, `β` on the real points,
the product of `realConv α F` and `realConv β F'` is the product of `F` and `F'` times
∫∫ conj(α(x)) β(y) conj(e(x⁻¹y))/e(1) dy dx. -/
theorem IsForm.petersson_realConv_realConv (he : IsCuspKernel B e) (h : V.IsForm e F)
    (h' : V.IsForm e F') {α β : GInf E s → ℂ} (hα : Integrable α) (hβ : Integrable β) :
    V.petersson (realConv α F) (realConv β F') =
      (∫ x : GInf E s, ∫ y : GInf E s, conj (α x) * β y * (conj (e (x⁻¹ * y)) / e 1)) *
        V.petersson F F' := by
  obtain ⟨K, hK⟩ := h'.exists_level
  have hβ_bdd : IsBoundedMeasurable (realConv β F') :=
    (isAutomorphic_realConv K h'.isBoundedMeasurable h'.rat_mul hK hβ).2
  -- The product of two real translates depends only on `x⁻¹ * y`, through the rank one idempotent.
  have h_translates (x y : GInf E s) :
      V.petersson (fun g : G E s ↦ F (g * (x, 1))) (fun g : G E s ↦ F' (g * (y, 1))) =
        conj (e (x⁻¹ * y)) / e 1 * V.petersson F F' := by
    rw [h.petersson_comp_mul_right (h'.toIsAutomorphic.comp_mul_right (y, 1)),
      ← h.petersson_real_translate he h']
    simp [mul_assoc]
  -- Unfold the convolution with `β` in the right argument.
  have h_right (x : GInf E s) :
      V.petersson (fun g : G E s ↦ F (g * (x, 1))) (realConv β F') =
        ∫ y : GInf E s, β y * (conj (e (x⁻¹ * y)) / e 1 * V.petersson F F') := by
    simp only [petersson_realConv_right h'.isBoundedMeasurable hβ
      (h.isBoundedMeasurable.comp (measurable_mul_const (x, 1))), h_translates]
  -- Conjugate symmetry moves the convolution with `α` to the right argument and back.
  calc
    _ = conj (∫ x, α x * V.petersson (realConv β F') fun g ↦ F (g * (x, 1))) := by
      rw [← conj_petersson, petersson_realConv_right h.isBoundedMeasurable hα hβ_bdd]
    _ = ∫ x, conj (α x) * V.petersson (fun g ↦ F (g * (x, 1))) (realConv β F') := by
      simp [← integral_conj]
    _ = _ := by simp [h_right, mul_assoc, ← integral_const_mul, ← integral_mul_const]

end New.Space

end Petersson

/-! ## Poincaré series projected to forms -/

section Poincare

open MeasureTheory ENNReal New
variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {e : GInf E s → ℂ}

/-- Let `W i` be countably many measurable functions on `G` with `∑ i, ‖W i‖` bounded, whose sum is
left invariant under the rational points `V.Γ` and right invariant under the open subgroup `K` of
the finite points. Then the sum of the right convolutions of the `W i` with the idempotent kernel
`e` is an element of `levelSpace (V.formRep e) K`, that is a form of type `e` fixed by `K`. -/
theorem New.Space.exists_form_eq_tsum_of_fixesLeft (he : IsIdempotentKernel e)
    (K : OpenSubgroup (Gf E n)) {ι : Type*} [Countable ι] {W : ι → G E s → ℂ}
    (hW_meas : ∀ i : ι, Measurable (W i))
    (h_invariant : V.Γ.FixesLeft fun g : G E s ↦ ∑' i : ι, W i g)
    (h_level : HasLevel (fun g : G E s ↦ ∑' i : ι, W i g) K)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (h_le : ∀ g : G E s, ∑' i : ι, ‖W i g‖ₑ ≤ M) :
    ∃ y : levelSpace (V.formRep e) K.toSubgroup,
      (y.val : G E s → ℂ) = fun g : G E s ↦ ∑' i : ι, realConv e (W i) g := by
  -- The series is the convolution with `e` of the bounded sum of the `W i`.
  have h_bounded (g : G E s) : ‖∑' i : ι, W i g‖ ≤ M.toReal := by
    simpa using toReal_mono hM (enorm_tsum_le_tsum_enorm.trans (h_le g))
  -- Convolve term by term: the kernel is integrable and the sum of the norms is at most `M`.
  have h_termwise (g : G E s) :
      ∑' i : ι, realConv e (W i) g = realConv e (fun x : G E s ↦ ∑' i : ι, W i x) g := by
    have := he.continuous.measurable
    simp only [realConv, ← tsum_mul_left]
    refine (hasSum_integral_of_lintegral_tsum_lt_top ?_).tsum_eq
    calc ∫⁻ x : GInf E s, ∑' i : ι, ‖e x * W i (g * (x, 1))‖ₑ
        ≤ ∫⁻ x : GInf E s, ‖e x‖ₑ * M := by
          simp only [enorm_mul, ENNReal.tsum_mul_left]
          grw [h_le]
      _ < ⊤ := by
          rw [lintegral_mul_const' _ _ hM]
          exact mul_lt_top he.integrable.hasFiniteIntegral hM.lt_top
  simp only [h_termwise]
  exact exists_form_eq_realConv K ⟨by fun_prop, M.toReal, h_bounded⟩ h_invariant h_level he

/-- **Poincaré series.** Let the sum of countably many measurable `W i`, with `∑ i, ‖W i‖` bounded,
be the sum over `V.Γ` of the left translates of one function `c` that is right invariant under the
open subgroup `K` of the finite points. Then the sum of the right convolutions of the `W i` with
the idempotent kernel `e` is a form of type `e` fixed by `K`. -/
theorem New.Space.exists_form_eq_tsum (he : IsIdempotentKernel e) (K : OpenSubgroup (Gf E n))
    {ι : Type*} [Countable ι] {W : ι → G E s → ℂ} (hW_meas : ∀ i : ι, Measurable (W i))
    {c : G E s → ℂ} (hc_level : HasLevel c K)
    (h_sum : ∀ g : G E s, ∑' γ : V.Γ, c (γ.val * g) = ∑' i : ι, W i g) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h_le : ∀ g : G E s, ∑' i : ι, ‖W i g‖ₑ ≤ M) :
    ∃ y : levelSpace (V.formRep e) K.toSubgroup,
      (y.val : G E s → ℂ) = fun g : G E s ↦ ∑' i : ι, realConv e (W i) g := by
  have h_invariant : V.Γ.FixesLeft fun g : G E s ↦ ∑' i : ι, W i g := fun γ hγ g ↦ by
    simpa [← h_sum, mul_assoc] using (Equiv.mulRight (⟨γ, hγ⟩ : V.Γ)).tsum_eq fun δ ↦ c (δ * g)
  have h_level : HasLevel (fun g : G E s ↦ ∑' i : ι, W i g) K := fun k hk g ↦ by
    simp only [← h_sum, ← mul_assoc, hc_level k hk]
  exact exists_form_eq_tsum_of_fixesLeft he K hW_meas h_invariant h_level hM h_le

end Poincare
