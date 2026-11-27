import Lib.Adelic.Reduction.DefiniteClassSums

/-!
# Automorphic forms on adelic unitary groups, the Petersson product and rapid decay

This file studies functions on the adelic unitary group G = G_∞ × G_f of a hermitian space V over E
with signs s. Here Γ = `V.Γ` is its group of rational points, and `V.quotMeasure` is the measure for
integrals over Γ\G. The forms of type e (see `New.Space.IsForm` below) make up an inner product
space under the Petersson product and carry an action of G_f. The height `New.Space.height` is the
inverse of the first minimum `New.Space.firstMinimum`, cut off at `1`. Moderate growth and rapid
decay are measured against the height, and the rapidly decaying automorphic functions form a
subrepresentation. When Γ is cocompact, in particular when all signs of V are equal, every
automorphic function has rapid decay.

## Main definitions and results

* `New.Space.IsAutomorphic`: continuous, left Γ-invariant functions with a level.
* `New.Space.IsForm`: bounded automorphic functions that are fixed by convolution with a kernel e if
  e is integrable (for e not integrable this condition is empty). A form is bounded and measurable
  (`IsBoundedMeasurable`, which follows from bounded and continuous), hence lies in L²(Γ\G).
* `New.Space.Form`: the space of these forms, an inner product space under the Petersson product
  `New.Space.petersson`, with the action `New.Space.formRep` of G_f.
* `New.Space.rapidFunctions`: the automorphic functions of rapid decay form a subrepresentation.
* `New.Space.isRapid_of_isCocompact`: continuous Γ-invariant functions are rapid when Γ is
  cocompact.
* `New.Space.IsAutomorphic.mem_rapidFunctions`: automorphic functions are rapid when all signs are
  equal.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.Space.Γ`: for a space (J, x), the subgroup x^{-1} U(J)(E) x of G, the image of the rational
  unitary group.
* `New.GInf`: the archimedean unitary group G_∞ for signs s: one copy of the complex unitary group
  U(diag s) for each infinite place of E.
* `New.Space.IsModerate`, `New.Space.IsRapid`: |F| ≤ C·ht^B for some C and B; |F|·ht^B is bounded
  for every B.

## Relation to the literature

Known result: automorphic forms on unitary groups and their rapid decay. Cusp forms are treated in
`Lib.Adelic.AutomorphicForms.Cuspidality`.
-/

noncomputable section

/-!
## Automorphic functions, automorphic forms and the Petersson product

* `New.typeKernel`, `New.realConv`: the product kernel on G_∞ of given parameters, and right
  convolution over G_∞.
* `New.ThetaKernel`: the data of a kernel on the product of two groups that is invariant under the
  rational points; it is used for theta lifts of forms.
-/

section Defs

open MeasureTheory Submodule

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  (V : Space E n s) (e : GInf E s → ℂ) (F F' : G E s → ℂ)

/-- The function e_λ(x) = ∏_w e_{λ_w}(x_w) on G_∞, for a family of doubled parameters l_w = 2λ_w. It
is the product over the infinite places of the functions `dsKernel` on U(diag s), each the formal
degree times the conjugate of the discrete series coefficient. -/
abbrev typeKernel (l : NumberField.InfinitePlace E → n → ℤ) (s : n → ℤˣ) (x : GInf E s) : ℂ :=
  ∏ w : NumberField.InfinitePlace E, dsKernel (l w) (x w)

/-- Right convolution over the real points: R(k)F(g) = ∫_{G_∞} k(x) F(gx) dx, for k on G_∞ and F
on G. -/
def realConv (k : GInf E s → ℂ) (F : G E s → ℂ) (g : G E s) : ℂ :=
  ∫ x : GInf E s, k x * F (g * (x, 1))

variable (E s) in
/-- The representation of G_f on complex functions on G by right translation. -/
abbrev finRightRep : Representation ℂ (Gf E n) (G E s → ℂ) :=
  (rightRegular ℂ (G E s) ℂ).comp (MonoidHom.inr (GInf E s) (Gf E n))

/-- A theta kernel (g, h, φ) ↦ θ(ω(g, h) φ) for the spaces S and T: an action ω of the product of
their groups on a normed space X and a functional θ on X, such that ω is jointly continuous and the
kernel is left invariant under Γ_S × Γ_T. -/
structure ThetaKernel {n' : Type} [Fintype n'] [DecidableEq n'] {t : n' → ℤˣ}
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (S : Space E n s) (T : Space E n' t) where
  /-- The action of the product of the groups of S and T on X by continuous linear maps. -/
  ω : G E s × G E t →* X →L[ℂ] X
  /-- The linear functional θ on X. -/
  θ : X →L[ℂ] ℂ
  /-- The action `(p, φ) ↦ ω p φ` is jointly continuous. -/
  continuous : Continuous ↿(ω · ·)
  /-- The kernel is invariant under left multiplication by rational points of both groups. -/
  rat_mul {γ : G E s} {γ' : G E t} :
      γ ∈ S.Γ → γ' ∈ T.Γ →
      ∀ (g : G E s) (k : G E t) (φ : X), θ (ω (γ * g, γ' * k) φ) = θ (ω (g, k) φ)

attribute [fun_prop] ThetaKernel.continuous

namespace Space

/-- F on G is automorphic: continuous, left Γ-invariant, and right invariant under some open
subgroup of G_f. -/
structure IsAutomorphic where
  /-- `F` is continuous. -/
  continuous : Continuous F
  /-- `F` is invariant under left multiplication by rational points. -/
  rat_mul : V.Γ.FixesLeft F
  /-- `F` has a level: it is right invariant under an open subgroup of the finite points. -/
  exists_level : ∃ K : OpenSubgroup (Gf E n), HasLevel F K

lemma isAutomorphic_const (c : ℂ) : V.IsAutomorphic fun _ : G E s ↦ c where
  continuous := continuous_const
  rat_mul _ _ _ := rfl
  exists_level := ⟨⊤, fun _ _ _ ↦ rfl⟩

/-- The Petersson product ⟨F, F'⟩ = ∫_{Γ\G} conj(F) F', taken with the measure
`New.Space.quotMeasure`. -/
def petersson : ℂ := ∫ g : G E s, starRingEnd ℂ (F g) * F' g ∂V.quotMeasure

/-- F is a form of type e, for a function e on G_∞: F is automorphic, bounded, and fixed by right
convolution with e if e is integrable. For e not integrable the last condition is empty, so that
every bounded automorphic function is then a form of type e. The forms of parameter λ are those of
type e_λ = `New.typeKernel l s`, with l = 2λ. -/
structure IsForm extends V.IsAutomorphic F where
  /-- `F` is bounded. -/
  bounded : ∃ C : ℝ, ∀ g : G E s, ‖F g‖ ≤ C
  /-- If `e` is integrable, right convolution with `e` over the real points fixes `F`. -/
  realConv_eq : Integrable e → realConv e F = F

variable {V e F F'}

/-- For automorphic functions F, F' and a function f of two complex variables that is jointly
continuous, the function g ↦ f(F(g), F'(g)) is automorphic. The continuity may be omitted when
`fun_prop` proves it. -/
lemma IsAutomorphic.map₂ (hF : V.IsAutomorphic F) (hF' : V.IsAutomorphic F') (f : ℂ → ℂ → ℂ)
    (hf : Continuous ↿f := by fun_prop) :
    V.IsAutomorphic fun g : G E s ↦ f (F g) (F' g) := by
  obtain ⟨h_cont, h_rat, K, hK⟩ := hF
  obtain ⟨h_cont', h_rat', L, hL⟩ := hF'
  exact
    { continuous := by fun_prop
      rat_mul := fun γ hγ g ↦ by simp only [h_rat γ hγ g, h_rat' γ hγ g]
      -- the intersection of the two levels is a level
      exists_level := ⟨K ⊓ L, fun k hk g ↦ by simp only [hK k hk.1 g, hL k hk.2 g]⟩ }

lemma IsAutomorphic.conj (hF : V.IsAutomorphic F) : V.IsAutomorphic (star F) :=
  hF.map₂ hF fun _ z ↦ star z

/-- A right translate g ↦ F(ga) of an automorphic function F by a point a of G is automorphic. -/
lemma IsAutomorphic.comp_mul_right (hF : V.IsAutomorphic F) (a : G E s) :
    V.IsAutomorphic fun g : G E s ↦ F (g * a) := by
  obtain ⟨h_cont, h_rat, K, hK⟩ := hF
  -- the translate by `a` has the level `K` conjugated by `a.2`
  let conjLevel : OpenSubgroup (Gf E n) :=
    K.comap (MulAut.conj a.2).symm (.mul_const (by fun_prop) _)
  refine ⟨by fun_prop, fun γ hγ g ↦ by rw [mul_assoc, h_rat γ hγ], conjLevel, fun k hk g ↦ ?_⟩
  have h_conj : a.2⁻¹ * k * a.2 ∈ K := hk
  calc
    F (g * (1, k) * a) = F (g * a * (1, a.2⁻¹ * k * a.2)) := by simp [Prod.mul_def, mul_assoc]
    _ = F (g * a) := hK _ h_conj _

/-- The Petersson product is definite: an automorphic function F that is square integrable on
Γ\G and has ⟨F, F⟩ = 0 vanishes everywhere. -/
lemma IsAutomorphic.eq_zero_of_petersson_self (h : V.IsAutomorphic F)
    (hF : MemLp F 2 V.quotMeasure) (h_pet : V.petersson F F = 0) :
    F = 0 := by
  -- `∫ ‖F‖ ^ 2 = 0`, so `F` vanishes almost everywhere on the quotient
  have h_int : ∫ g, ‖F g‖ ^ 2 ∂V.quotMeasure = 0 := by
    simpa [RCLike.conj_mul, ← Complex.ofReal_pow, integral_complex_ofReal, petersson] using h_pet
  have h_ae : ∀ᵐ g ∂V.quotMeasure, F g = 0 := by
    simpa [Filter.EventuallyEq] using
      (integral_eq_zero_iff_of_nonneg (fun g ↦ sq_nonneg _) hF.norm.integrable_sq).1 h_int
  -- the zero set of `F` is stable under `V.Γ`, hence dense; and `F` is continuous
  have h_dense : Dense {g | F g = 0} :=
    dense_of_ae_orbitMeasure (fun (γ : V.Γ) g hg ↦ (h.rat_mul γ γ.2 g).trans hg) h_ae
  exact h.continuous.ext_on h_dense continuous_zero fun _ hg ↦ hg

lemma IsForm.isBoundedMeasurable (hF : V.IsForm e F) : IsBoundedMeasurable F :=
  .of_continuous hF.bounded hF.continuous

lemma IsForm.memLp (hF : V.IsForm e F) : MemLp F 2 V.quotMeasure :=
  hF.isBoundedMeasurable.memLp_top.mono_exponent le_top

/-- The right translate g ↦ F(g·(1, a)) of a form F of type e by a finite point a is again a form
of type e. -/
lemma IsForm.comp_mul_right (hF : V.IsForm e F) (a : Gf E n) :
    V.IsForm e fun g : G E s ↦ F (g * (1, a)) := by
  obtain ⟨h_aut, ⟨C, hC⟩, h_fix⟩ := hF
  refine ⟨h_aut.comp_mul_right _, ⟨C, fun g ↦ hC _⟩, fun he ↦ funext fun g ↦ ?_⟩
  -- the finite point `(1, a)` commutes with the real points over which `realConv` integrates
  have h_comm (x : GInf E s) : g * (x, 1) * (1, a) = g * (1, a) * (x, 1) := by simp [mul_assoc]
  simpa only [realConv, h_comm] using congrFun (h_fix he) (g * (1, a))

variable (V e)

lemma isForm_zero : V.IsForm e 0 where
  toIsAutomorphic := V.isAutomorphic_const 0
  bounded := ⟨0, by simp⟩
  realConv_eq := by simp [funext_iff, realConv]

/-- A linear combination aF + bF' of two forms F, F' of type e (bounded automorphic functions on G
fixed by convolution with e if e is integrable) is a form of type e. -/
lemma IsForm.smul_add_smul (hF : V.IsForm e F) (hF' : V.IsForm e F') (a b : ℂ) :
    V.IsForm e (a • F + b • F') := by
  obtain ⟨C, hC⟩ := hF.bounded
  obtain ⟨C', hC'⟩ := hF'.bounded
  refine ⟨hF.toIsAutomorphic.map₂ hF'.toIsAutomorphic fun z w ↦ a * z + b * w,
    ⟨‖a‖ * C + ‖b‖ * C', fun g ↦ ?_⟩, fun he ↦ funext fun g ↦ ?_⟩
  · exact norm_add_le_of_le (norm_mul_le_of_le le_rfl (hC g)) (norm_mul_le_of_le le_rfl (hC' g))
  · -- `e` is integrable and forms are bounded, so the integral `realConv e` is linear on them.
    have h_int {H : G E s → ℂ} (hH : V.IsForm e H) (c : ℂ) :
        Integrable fun x : GInf E s ↦ c • (e x * H (g * (x, 1))) :=
      (hH.isBoundedMeasurable.integrable_mul_comp he fun x ↦ g * (x, 1)).fun_smul c
    calc
      realConv e (a • F + b • F') g
          = ∫ x : GInf E s, a • (e x * F (g * (x, 1))) + b • (e x * F' (g * (x, 1))) := by
        simp [realConv, mul_add, mul_left_comm]
      _ = a • realConv e F g + b • realConv e F' g := by
        simp only [realConv, integral_add (h_int hF a) (h_int hF' b), integral_smul]
      _ = (a • F + b • F') g := by simp [hF.realConv_eq he, hF'.realConv_eq he]

/-- The forms of type e for V, as a submodule of the complex functions on G. -/
def formSubmodule : Submodule ℂ (G E s → ℂ) :=
  ofLinearComb {F : G E s → ℂ | V.IsForm e F} ⟨0, isForm_zero V e⟩ fun F hF F' hF' a b ↦
    show V.IsForm e (a • F + b • F') from hF.smul_add_smul V e hF' a b

/-- The complex vector space of forms of type e for V, namely the type of elements of
`New.Space.formSubmodule`. -/
def Form : Type :=
  V.formSubmodule e
  deriving AddCommGroup, Module ℂ

-- A form is read as a function on the adelic points.
instance : CoeFun (V.Form e) fun _ : V.Form e ↦ G E s → ℂ := ⟨(·.val)⟩

variable {V e} in
lemma Form.isForm (F : V.Form e) : V.IsForm e F := F.property

/-- The linear map that sends a form of type e to its class in L²(Γ\G), taken for the measure
`New.Space.quotMeasure`. -/
def Form.toL2 : V.Form e →ₗ[ℂ] Lp ℂ 2 V.quotMeasure where
  toFun F := F.isForm.memLp.toLp F
  map_add' F F' := F.isForm.memLp.toLp_add F'.isForm.memLp
  map_smul' c F := F.isForm.memLp.toLp_const_smul c

variable {V e} in
/-- The Petersson product of two forms of type e is the inner product of their classes in
L²(Γ\G). -/
lemma Form.petersson_eq_inner_toL2 (F F' : V.Form e) :
    V.petersson F F' = inner ℂ (toL2 V e F) (toL2 V e F') := by
  have hF : toL2 V e F =ᵐ[V.quotMeasure] F := F.isForm.memLp.coeFn_toLp
  have hF' : toL2 V e F' =ᵐ[V.quotMeasure] F' := F'.isForm.memLp.coeFn_toLp
  rw [L2.inner_def, petersson]
  refine integral_congr_ae ?_
  filter_upwards [hF, hF'] with g hg hg'
  rw [hg, hg', RCLike.inner_apply']

/-- The positive definite inner product on forms of type e given by the Petersson product, the
integral of conj(F)·F' over Γ\G. Symmetry, positivity and sesquilinearity are those of the inner
product of L²(Γ\G); definiteness holds because forms are continuous. -/
instance peterssonCore : InnerProductSpace.Core ℂ (V.Form e) where
  inner F F' := V.petersson F F'
  conj_inner_symm F F' := by simp only [Form.petersson_eq_inner_toL2, inner_conj_symm]
  re_inner_nonneg F := by simp only [Form.petersson_eq_inner_toL2, inner_self_nonneg]
  add_left F F' F'' := by simp only [Form.petersson_eq_inner_toL2, map_add, inner_add_left]
  smul_left F F' c := by simp only [Form.petersson_eq_inner_toL2, map_smul, inner_smul_left]
  definite F hF := Subtype.ext (F.isForm.eq_zero_of_petersson_self F.isForm.memLp hF)

instance : NormedAddCommGroup (V.Form e) := (peterssonCore V e).toNormedAddCommGroup

instance : InnerProductSpace ℂ (V.Form e) := .ofCore (peterssonCore V e).toCore

/-- The representation of G_f on forms of type e by right translation. -/
def formRep : Representation ℂ (Gf E n) (V.Form e) :=
  (finRightRep E s).subrepresentation (V.formSubmodule e)
    fun a _ hF ↦ IsForm.comp_mul_right hF a

end Space

end New

end Defs

/-!
## Heights and rapidly decaying functions

* `New.Space.exists_height_le_mul`: the height changes by a bounded factor under rational points on
  the left and a compact set on the right.
-/

section Growth

open Matrix.Norms.L2Operator

namespace New.Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {F M : G E s → ℂ} {B : ℕ} {K : Set (G E s)}

/-! ### The height -/

/-- The height is at least 1, as the first minimum is cut off at 1. -/
theorem one_le_height (g : G E s) : 1 ≤ V.height g :=
  (one_le_inv₀ (V.move g).firstMinimum_pos).mpr firstMinimum_le_one

@[simp]
theorem height_pos (g : G E s) : 0 < V.height g := one_pos.trans_le (one_le_height g)

/-- For compact K ⊆ G there is C ≥ 1 such that ht(k) ≤ C·ht(g) whenever g⁻¹γk ∈ K. Here γ runs over
the rational unitary group U(J)(E) of V, mapped into G by `New.Space.ratEmbed`, and ht is the
height of V, the inverse of the first minimum cut off at 1. -/
theorem exists_height_le_mul (hK : IsCompact K) :
    ∃ C ≥ (1 : ℝ), ∀ (γ : U V.J) (g k : G E s),
      g⁻¹ * V.ratEmbed γ * k ∈ K → V.height k ≤ C * V.height g := by
  -- One denominator `c` and one bound `R` of the operator norms at infinity serve all of `K`.
  -- A vector `y` of the lattice at `k` gives the vector `c γ y` of the lattice at `g`, at most
  -- `c * R` times as long; so the first minimum at `g` is at most `max 1 (c * R)` times
  -- that at `k`.
  obtain ⟨c, hc, h_lat⟩ := V.exists_smul_mulVec_mem_latticeBall (hK.image continuous_snd)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ K, ∀ w : NumberField.InfinitePlace E,
      ‖(x.1 w).val.val‖ ≤ R := by
    obtain ⟨R, hR⟩ :=
      hK.exists_bound_of_continuousOn (f := fun x w ↦ (x.1 w).val.val) (by fun_prop)
    exact ⟨R, fun x hx w ↦ (norm_le_pi_norm _ w).trans (hR x hx)⟩
  refine ⟨max 1 (c * R), le_max_left _ _, fun γ g k h_mem ↦ ?_⟩
  have short_le (y : n → E) (hy : y ∈ (V.move k).baseLattice) (y_ne : y ≠ 0) :
      (V.move g).firstMinimum ≤ max 1 (c * R) * ‖(V.move k).archCoords y‖ := by
    obtain ⟨mem_lat, norm_le⟩ : (c : E) • γ.val.val.mulVec y ∈
        (V.move g).latticeBall (c * R * ‖(V.move k).archCoords y‖) :=
      h_lat (Set.mem_image_of_mem Prod.snd h_mem) (hR _ h_mem) y hy
    have mulVec_ne : γ.val.val.mulVec y ≠ 0 := show γ • y ≠ 0 from (smul_ne_zero_iff_ne γ).2 y_ne
    have image_ne : (c : E) • γ.val.val.mulVec y ≠ 0 :=
      smul_ne_zero (Nat.cast_ne_zero.2 hc) mulVec_ne
    grw [firstMinimum_le mem_lat image_ne, norm_le, ← le_max_right]
  -- By `le_firstMinimum_iff` this is `short_le` together with the bound `1` on the first minimum at
  -- `g`.
  have h_min : (max 1 (c * R) * V.height g)⁻¹ ≤ (V.move k).firstMinimum := by
    simpa [le_firstMinimum_iff, height, field] using short_le
  exact inv_le_of_inv_le₀ (by simp) h_min

/-- For a compact set K ⊆ G, a real C and a natural number B, the function g ↦ C·ht(g)^B is bounded
above on the set of g that a point of Γ moves into K. Here ht is the height of V, the inverse of
the first minimum cut off at 1. -/
theorem exists_mul_height_pow_le (hK : IsCompact K) (C : ℝ) :
    ∃ D : ℝ, ∀ᵉ (g : G E s) (γ ∈ V.Γ), γ * g ∈ K → C * V.height g ^ B ≤ D := by
  obtain ⟨C', hC'_one, hC'⟩ := V.exists_height_le_mul hK
  refine ⟨|C| * (C' * V.height 1) ^ B, fun g _ ⟨γ, hγ⟩ hg ↦ ?_⟩
  -- As `γ * g ∈ K`, the height of `g` is comparable to the height of `1`.
  have h_ht : V.height g ≤ C' * V.height 1 := hC' γ 1 g (by simpa [hγ] using hg)
  have h_nonneg : 0 ≤ V.height g := (height_pos g).le
  grw [le_abs_self C, h_ht]

/-! ### Rapidly decaying functions -/

theorem IsRapid.bounded (hF : V.IsRapid F) : ∃ C : ℝ, ∀ g : G E s, ‖F g‖ ≤ C := by
  simpa using hF 0

/-- The product of a function M of moderate growth (|M| ≤ C·ht^b for some C and b) and a function F
of rapid decay (|F|·ht^B bounded for every B) has rapid decay. Here ht is the height of V. -/
lemma IsRapid.mul (hF : V.IsRapid F) (hM : V.IsModerate M) : V.IsRapid (M * F) := by
  intro B
  obtain ⟨C, b, hC⟩ := hM
  obtain ⟨D, hD⟩ := hF (b + B)
  refine ⟨|C| * D, fun g ↦ ?_⟩
  have h_nonneg : 0 ≤ V.height g := (height_pos g).le
  calc
    ‖M g * F g‖ * V.height g ^ B ≤ |C| * V.height g ^ b * ‖F g‖ * V.height g ^ B := by
      grw [norm_mul, hC g, le_abs_self C]
    _ = |C| * (‖F g‖ * V.height g ^ (b + B)) := by ring
    _ ≤ |C| * D := by grw [hD g]

/-- If F has rapid decay (|F|·ht^B is bounded for every B), then so has its right translate
g ↦ F(gx) by any point x of G. -/
theorem IsRapid.comp_mul_right (hF : V.IsRapid F) {x : G E s} :
    V.IsRapid fun g : G E s ↦ F (g * x) := by
  intro B
  obtain ⟨D, hD⟩ := hF B
  obtain ⟨C, hC_one, hC⟩ := V.exists_height_le_mul (isCompact_singleton (x := x⁻¹))
  refine ⟨C ^ B * D, fun g ↦ ?_⟩
  -- `(g * x)⁻¹ * g = x⁻¹`, so the heights of `g` and `g * x` are comparable.
  have h_ht : V.height g ≤ C * V.height (g * x) := hC 1 (g * x) g (by simp)
  have h_nonneg : 0 ≤ V.height g := (height_pos g).le
  calc
    ‖F (g * x)‖ * V.height g ^ B ≤ ‖F (g * x)‖ * (C * V.height (g * x)) ^ B := by gcongr
    _ = C ^ B * (‖F (g * x)‖ * V.height (g * x) ^ B) := by ring
    _ ≤ C ^ B * D := by grw [hD]

/-- A continuous function of rapid decay is integrable for the measure `New.Space.quotMeasure` of
Γ\G. -/
theorem IsRapid.integrable (hF : V.IsRapid F) (h_cont : Continuous F) :
    MeasureTheory.Integrable F V.quotMeasure :=
  (IsBoundedMeasurable.of_continuous hF.bounded h_cont).memLp_top.integrable le_top

/-- A linear combination aF + bF' of two functions of rapid decay (|F|·ht^B bounded for every B,
with ht the height of V) has rapid decay. -/
theorem IsRapid.smul_add_smul {F' : G E s → ℂ} (hF : V.IsRapid F) (hF' : V.IsRapid F')
    (a b : ℂ) : V.IsRapid (a • F + b • F') := by
  intro B
  obtain ⟨C, hC⟩ := hF B
  obtain ⟨C', hC'⟩ := hF' B
  refine ⟨‖a‖ * C + ‖b‖ * C', fun g ↦ ?_⟩
  have h_nonneg : 0 ≤ V.height g := (height_pos g).le
  calc
    ‖a • F g + b • F' g‖ * V.height g ^ B
        ≤ ‖a‖ * (‖F g‖ * V.height g ^ B) + ‖b‖ * (‖F' g‖ * V.height g ^ B) := by
      grw [norm_add_le, norm_smul, norm_smul, add_mul, mul_assoc, mul_assoc]
    _ ≤ ‖a‖ * C + ‖b‖ * C' := by grw [hC, hC']

/-- The automorphic functions of rapid decay for `V`, as a subrepresentation of the functions on G
under right translation by G_f. -/
noncomputable def rapidFunctions : Subrepresentation (finRightRep E s) where
  toSubmodule :=
    Submodule.ofLinearComb {F : G E s → ℂ | V.IsAutomorphic F ∧ V.IsRapid F}
      ⟨0, V.isAutomorphic_const 0, fun B ↦ ⟨0, by simp⟩⟩
      fun F ⟨hF_aut, hF_rapid⟩ F' ⟨hF'_aut, hF'_rapid⟩ a b ↦
        ⟨hF_aut.map₂ hF'_aut fun z w ↦ a * z + b * w, hF_rapid.smul_add_smul hF'_rapid a b⟩
  apply_mem_toSubmodule a _ := fun ⟨hF_aut, hF_rapid⟩ ↦
    ⟨hF_aut.comp_mul_right (1, a), hF_rapid.comp_mul_right⟩

/-- The complex conjugate of a rapidly decaying automorphic function is one as well. -/
theorem star_mem_rapidFunctions (hF : F ∈ V.rapidFunctions) : star F ∈ V.rapidFunctions := by
  obtain ⟨hF_aut, hF_rapid⟩ := hF
  exact ⟨hF_aut.conj, fun B ↦ by simpa only [Pi.star_apply, norm_star] using hF_rapid B⟩

end New.Space

end Growth

/-! ## Rapid decay on definite spaces -/

namespace New.Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {F : G E s → ℂ}

/-- If the group Γ of rational points is cocompact, a continuous left Γ-invariant function F has
rapid decay: |F|·ht^B is bounded for every B, with ht the height of V. -/
lemma isRapid_of_isCocompact (hF : Continuous F) (h_inv : V.Γ.FixesLeft F)
    (h_cocompact : V.Γ.IsCocompact) : V.IsRapid F := by
  intro B
  obtain ⟨K, hK, h_cover⟩ : ∃ K : Set (G E s), IsCompact K ∧ ∀ g, ∃ γ ∈ V.Γ, γ * g ∈ K :=
    h_cocompact
  -- `F` is bounded on `K`, and the height is bounded on the `Γ`-orbit of `K`, the whole group.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g ∈ K, ‖F g‖ ≤ C :=
    hK.exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ g, ∀ γ ∈ V.Γ, γ * g ∈ K → C * V.height g ^ B ≤ D :=
    exists_mul_height_pow_le hK C
  refine ⟨D, fun g ↦ ?_⟩
  obtain ⟨γ, hγ, hγg⟩ := h_cover g
  calc
    ‖F g‖ * V.height g ^ B = ‖F (γ * g)‖ * V.height g ^ B := by rw [h_inv γ hγ]
    _ ≤ C * V.height g ^ B := mul_le_mul_of_nonneg_right (hC _ hγg) (pow_pos (height_pos g) B).le
    _ ≤ D := hD g γ hγ hγg

/-- On a definite space (all signs `s i` are equal) every automorphic function F (continuous, left
Γ-invariant, with a level) has rapid decay (|F|·ht^B is bounded for every B), so it lies in
`rapidFunctions`. -/
lemma IsAutomorphic.mem_rapidFunctions (hF : V.IsAutomorphic F)
    (h_definite : ∀ i j : n, s i = s j) : F ∈ V.rapidFunctions :=
  ⟨hF, isRapid_of_isCocompact hF.continuous hF.rat_mul (V.isCocompact_of_definite h_definite)⟩

end New.Space

end
