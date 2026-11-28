import Lib.Adelic.Witt.WittTheorem

/-!
# Measures on hermitian quadrics: existence and uniqueness of disintegrations

This file develops measure theory on hermitian quadrics over a "place" `A`. The result is a measure
that is written `Dirac(h(x, x) - Γ) dx` and is determined by the disintegration property. Quadrics
and disintegrations are indexed by skew elements `b`, with `Γ = δ⁻¹ * b` for a skew unit δ.

* `New.Floors.Place`: the data and properties of a place. Here `skewMeasure`, written ν, is a Haar
  measure on the skew elements, and `skewUnit`, written δ, is a skew unit. For hermitian Γ, the
  element δΓ is skew (`New.Floors.Place.skewUnitMul`).
* `New.Floors.Place.flatChart`, `New.Floors.Place.quadricMeasure`: for hermitian `T`, an explicit
  chart of `h(x, x) = δ⁻¹ * b`, and the image of the flat measure under it. Here `h` is a hyperbolic
  plane plus `T` (`New.Floors.planeSumGram`).
* `New.Floors.Place.IsDisintegration`: disintegrations along `h(x, x)`. For hermitian `T`, the chart
  measures form a disintegration of the volume (`New.Floors.Place.isDisintegration_quadricMeasure`).
  Disintegrations are unique at every skew `b` (`New.Floors.Place.IsDisintegration.unique`). They
  move along a matrix `M` with `Mᴴ * J * M = T` that has a left inverse
  (`New.Floors.Place.IsDisintegration.map`).

Notation: for a ring with involution, `skewAdjoint A` is the group of elements with `star x = -x`,
and `x⁻¹ʳ` is the ring inverse, which is zero at non-units. The vector `x ⊕ᵥ y` on a disjoint union
of index sets is `x` on the first part and `y` on the second. The group `U T` consists of the
invertible matrices g with `gᴴ * T * g = T`.
-/

namespace New.Floors

/-- A choice of an element τ = `element` with τ + τ̄ = 1 in a commutative ring with involution. -/
class TraceOne (A : Type*) [CommRing A] [StarRing A] where
  /-- The chosen element τ. -/
  element : A
  /-- τ has trace one: τ + τ̄ = 1. -/
  element_add_star : element + star element = 1

instance {A : Type*} [Field A] [CharZero A] [StarRing A] : TraceOne A where
  element := 2⁻¹
  element_add_star := by norm_num

open Matrix MeasureTheory Measure ENNReal Sum Ring Units Function Set TraceOne

variable (A : Type) [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]

/-- A place, such as ℂ or a finite product of completions: a locally compact star ring A with Haar
volume, an element τ = `element` of trace one, a skew unit δ, a Haar measure ν on the skew elements,
a modulus `modulus` that describes how matrices scale the volume, a unitary additive character ψ,
and a bound c = `kernelBound` in [0, ∞] such that some kernel has Fourier transform of L¹ norm at
most `c`. -/
class Place extends IsTopologicalRing A, ContinuousStar A, LocallyCompactSpace A, PolishSpace A,
  BorelSpace A, (volume : Measure A).IsAddHaarMeasure, TraceOne A where
  /-- A unit δ, skew by `star_skewUnit`. -/
  skewUnit : Aˣ
  /-- A measure ν on the skew elements, Haar by `haar`. -/
  skewMeasure : Measure (skewAdjoint A)
  /-- The modulus, a multiplicative map to [0, ∞]. -/
  modulus : A →* ℝ≥0∞
  /-- An additive character ψ. -/
  ψ : AddChar A ℂ
  /-- A bound for the L¹ norm of the Fourier transform of the kernel in
  `exists_plancherel_kernel`. -/
  kernelBound : ℝ≥0∞
  /-- ν is an additive Haar measure. -/
  [haar : IsAddHaarMeasure skewMeasure]
  /-- ψ is continuous. -/
  continuous_psi : Continuous ψ
  /-- The modulus is measurable. -/
  measurable_modulus : Measurable modulus
  /-- δ is skew: δ̄ = −δ. -/
  star_skewUnit : star skewUnit.1 = -skewUnit
  /-- The map (a, b) ↦ τδ⁻¹a + b on pairs of skew elements carries ν × ν to the volume of A. -/
  measurePreserving_split : MeasurePreserving
    (fun p : skewAdjoint A × skewAdjoint A ↦ element * skewUnit⁻¹ * p.1 + p.2)
    (skewMeasure.prod skewMeasure) volume
  /-- The modulus is invariant under conjugation and under negation. -/
  modulus_star_and_neg (x : A) : modulus (star x) = modulus x ∧ modulus (-x) = modulus x
  /-- An invertible matrix M maps the volume of Aⁿ to (`modulus` (det M))⁻¹ times itself. -/
  map_mulVec_volume (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n A) :
    IsUnit M.det → volume.map (M *ᵥ ·) = (modulus M.det)⁻¹ • volume
  /-- Almost every element is a unit. -/
  ae_isUnit : ∀ᵐ t : A, IsUnit t
  /-- On units, the power −1/2 of the modulus has a locally integrable majorant:
  (`modulus` u)⁻¹ ≤ |g(u)|² for some locally integrable g. -/
  exists_locallyIntegrable_bound :
    ∃ g : A → ℝ, LocallyIntegrable g volume ∧ ∀ u : Aˣ, (modulus u)⁻¹ ≤ ‖g u‖ₑ ^ 2
  /-- The values of ψ have absolute value one. -/
  norm_psi (x : A) : ‖ψ x‖ = 1
  /-- There is a continuous integrable G ≥ 0 with G(0) = 1 whose Fourier transform
  z ↦ ∫ G(v) ψ(v̄z) dv has L¹ norm at most c. -/
  exists_plancherel_kernel : ∃ G : A → ℝ,
    Continuous G ∧
    Integrable G ∧
    0 ≤ G ∧
    G 0 = 1 ∧
    ∫⁻ z : A, ‖∫ v : A, G v * ψ (star v * z)‖ₑ ≤ kernelBound

variable {A}

/-! ### Skew elements -/

/-- The skew element x − x̄ attached to x. -/
abbrev skewPart (x : A) : skewAdjoint A := ⟨x - star x, by simp [skewAdjoint]⟩

/-- The product xβ of a hermitian element x and a skew element β, as a skew element. -/
abbrev hermitianMul (x : A) (hx : star x = x) (β : skewAdjoint A) : skewAdjoint A :=
  ⟨x * β, by simp [skewAdjoint, hx]⟩

section

variable [IsTopologicalRing A] [ContinuousStar A] [PolishSpace A]

/-- The skew elements form a closed subset of `A`, so they inherit a Polish and a locally compact
topology. -/
instance isClosed_skewAdjoint : IsClosed (skewAdjoint A : Set A) :=
  isClosed_eq continuous_star continuous_neg

instance : PolishSpace (skewAdjoint A) := isClosed_skewAdjoint.polishSpace

instance [LocallyCompactSpace A] : LocallyCompactSpace (skewAdjoint A) :=
  isClosed_skewAdjoint.locallyCompactSpace

end

variable [P : Place A] {ι : Type} [Fintype ι] [DecidableEq ι] (u : Aˣ) (T : Matrix ι ι A)
  (b : skewAdjoint A) (μ : Measure (ι → A)) {κ : Type*} [Fintype κ]

/-! ### Lemmas on measures, and the hyperbolic plane plus a form -/

lemma measurableEmbedding_units_val : MeasurableEmbedding (val : Aˣ → A) :=
  continuous_val.measurableEmbedding val_injective

@[fun_prop]
lemma measurable_inverse : Measurable (inverse : A → A) :=
  measurableEmbedding_units_val.measurable_extend continuous_coe_inv.measurable measurable_const

/-- For a map f : Z → Z, a measure ζ on Z with ζ.map f = c⁻¹ • ζ, and c neither zero nor infinite,
the integral of g against ζ is c times the integral of g against the image ζ.map f. -/
lemma lintegral_eq_mul_lintegral_map {Z : Type*} [MeasurableSpace Z] {ζ : Measure Z} {f : Z → Z}
    {c : ℝ≥0∞} {g : Z → ℝ≥0∞} (h_map : ζ.map f = c⁻¹ • ζ) (hc_ne_zero : c ≠ 0)
    (hc_ne_top : c ≠ ∞) : ∫⁻ x : Z, g x ∂ζ = c * ∫⁻ x : Z, g x ∂ζ.map f := by
  simp [h_map, ENNReal.mul_inv_cancel_left hc_ne_zero hc_ne_top]

/-- For a measure ζ on Z and f, g : Z → [0, ∞], if p holds ζ-almost everywhere and f = g where p
holds, then f and g have the same lower integral. -/
lemma lintegral_congr_of_ae_imp {Z : Type*} [MeasurableSpace Z] {ζ : Measure Z} {p : Z → Prop}
    {f g : Z → ℝ≥0∞} (hp : ∀ᵐ x : Z ∂ζ, p x) (hfg : ∀ x : Z, p x → f x = g x) :
    lintegral ζ f = lintegral ζ g := lintegral_congr_ae (hp.mono hfg)

/-- For a measure ζ on Z and f, g : Z → [0, ∞], if p holds ζ-almost everywhere and f ≤ g where p
holds, then the lower integral of f is at most that of g. -/
lemma lintegral_le_of_ae_imp {Z : Type*} [MeasurableSpace Z] {ζ : Measure Z} {p : Z → Prop}
    {f g : Z → ℝ≥0∞} (hp : ∀ᵐ x : Z ∂ζ, p x) (hfg : ∀ x : Z, p x → f x ≤ g x) :
    lintegral ζ f ≤ lintegral ζ g := lintegral_mono_ae (hp.mono hfg)

/-- A continuous function f ≥ 0 of compact support has a finite integral against a measure ζ that
is finite on compact sets. -/
lemma lintegral_lt_top_of_hasCompactSupport {Z : Type*} [MeasurableSpace Z] {ζ : Measure Z}
    [TopologicalSpace Z] [BorelSpace Z] [IsFiniteMeasureOnCompacts ζ] {f : Z → NNReal}
    (hf : Continuous f) (hf_supp : HasCompactSupport f) : ∫⁻ y : Z, f y ∂ζ < ∞ := by
  have h_int : Integrable (fun y : Z ↦ (f y : ℝ)) ζ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hf_supp.comp_left NNReal.coe_zero)
  simp [lintegral_coe_eq_integral f h_int]

/-- Let F ≥ 0 be jointly continuous in x in X and y in Z, vanishing for y outside a compact set k,
and let ζ be finite on compact sets. Then x ↦ ∫ F(x, y) dζ(y) is continuous. -/
lemma continuous_lintegral_of_compact_support {X Z : Type*} [TopologicalSpace X]
    [MeasurableSpace Z] {ζ : Measure Z} [TopologicalSpace Z] [T2Space Z] [BorelSpace Z]
    [IsFiniteMeasureOnCompacts ζ] {k : Set Z} {F : X → Z → NNReal} (hk : IsCompact k)
    (hF : Continuous ↿F) (h_supp : ∀ (x : X) (y : Z), F x y ≠ 0 → y ∈ k) :
    Continuous fun x : X ↦ ∫⁻ y : Z, F x y ∂ζ := by
  have h_zero (x : X) (y : Z) (hy : y ∉ k) : (F x y : ℝ) = 0 := by simpa using mt (h_supp x y) hy
  -- Each `F x` is integrable, so its lower integral is the Bochner integral.
  have h_eq (x : X) : ∫⁻ y, F x y ∂ζ = .ofReal (∫ y, F x y ∂ζ) :=
    lintegral_coe_eq_integral (F x) (HasCompactSupport.integrable (.intro hk (h_zero x)))
  simp only [h_eq]
  exact continuous_ofReal.comp <| continuousOn_univ.1 <|
    continuousOn_integral_of_compact_support hk (by fun_prop) fun x y _ ↦ h_zero x y

omit [MeasureSpace A] [Place A] in
/-- Let F ≥ 0 be jointly continuous in a skew element x of A and y in Z, vanishing for y outside
a compact set k, and let ζ be finite on compact sets. Then x ↦ ∫ F(x, y) dζ(y) is continuous and
finite. -/
lemma continuous_lintegral_and_lt_top {Z : Type*} [MeasurableSpace Z] {ζ : Measure Z}
    [TopologicalSpace Z] [T2Space Z] [BorelSpace Z] [IsFiniteMeasureOnCompacts ζ] {k : Set Z}
    {F : skewAdjoint A → Z → NNReal} (hk : IsCompact k) (hF : Continuous ↿F)
    (h_supp : ∀ (x : skewAdjoint A) (y : Z), F x y ≠ 0 → y ∈ k) :
    Continuous (fun x : skewAdjoint A ↦ ∫⁻ y : Z, F x y ∂ζ) ∧
    ∀ x : skewAdjoint A, ∫⁻ y : Z, F x y ∂ζ < ∞ :=
  ⟨continuous_lintegral_of_compact_support hk hF h_supp, fun x ↦
    lintegral_lt_top_of_hasCompactSupport (hF.uncurry_left x)
      (.of_support_subset_isCompact hk (h_supp x))⟩

section

omit [DecidableEq ι]

/-- For a place A and finite index sets ι, κ, joining two vectors is a volume-preserving map
from A^ι × A^κ to A^(ι ⊔ κ). -/
lemma measurePreserving_sumElim : MeasurePreserving fun p : (ι → A) × (κ → A) ↦ p.1 ⊕ᵥ p.2 :=
  volume_measurePreserving_sumPiEquivProdPi_symm fun _ ↦ A

@[fun_prop]
lemma measurable_sumElim_pair : Measurable fun p : (ι → A) × (κ → A) ↦ p.1 ⊕ᵥ p.2 :=
  measurePreserving_sumElim.measurable

/-- For a place A and a finite index set ι, the map (s, t, w) ↦ (s, t) ⊕ w from A × A × A^ι to
vectors indexed by the disjoint union of Fin 2 and ι preserves the volume. -/
lemma measurePreserving_pair_sumElim :
    MeasurePreserving fun r : A × A × (ι → A) ↦ ![r.1, r.2.1] ⊕ᵥ r.2.2 := by
  have h_pair : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := A)).symm :=
    (volume_preserving_finTwoArrow A).symm
  exact (measurePreserving_sumElim.comp (h_pair.prod (.id _))).comp volume_preserving_prodAssoc.symm

end

/-- The Gram matrix of a hyperbolic plane plus the form T: block diagonal with blocks (0 1; 1 0)
and T. -/
abbrev planeSumGram : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) A := fromBlocks !![0, 1; 1, 0] 0 0 T

/-- The unitary group of the Gram matrix T is a Borel space. -/
instance : BorelSpace (U T) := inferInstance

namespace Place

attribute [instance] haar

instance : SigmaFinite P.skewMeasure := inferInstance

attribute [simp] norm_psi modulus_star_and_neg

attribute [fun_prop] continuous_psi measurable_modulus

attribute [simp, grind! .] element_add_star

/-- The flat chart of the quadric h(v, v) = δ⁻¹b in a hyperbolic plane (e, e') plus T:
(t, w, a) ↦ (t̄⁻¹τ(δ⁻¹b − h(w, w)) + ta)e + te' + w, with a skew. Here t̄⁻¹ is the ring inverse,
which is zero when t̄ is not a unit; the image point lies on the quadric when T is hermitian and t
is a unit. -/
noncomputable def flatChart : (A × (ι → A)) × skewAdjoint A → Fin 2 ⊕ ι → A
  | ((t, w), a) => ![(star t)⁻¹ʳ * element * (skewUnit⁻¹.val * b - star w ⬝ᵥ T *ᵥ w) + t * a, t] ⊕ᵥ
    w

/-- The image of dt dw dν(a) under the flat chart `New.Floors.Place.flatChart`. For hermitian T it
is the fiber measure dv / dh(v, v) on the quadric h(v, v) = δ⁻¹b
(`isDisintegration_quadricMeasure`).

This makes Weil's fiber measures for a submersion explicit for the map v ↦ h(v, v), which is a
submersion at points whose coordinate t is a unit. -/
noncomputable abbrev quadricMeasure : Measure (Fin 2 ⊕ ι → A) :=
  (volume.prod skewMeasure).map (flatChart T b)

/-! ### Disintegrations along the form, and scaling of the volume -/

/-- The family l_b, indexed by skew b, disintegrates μ along h(x, x) = x̄ᵀJx. For continuous
compactly supported f ≥ 0, the integrals ∫ f dl_b are finite and continuous in b. Moreover, for
measurable f, we have ∫ f(h(x, x), x) dμ = ∬ f(δ⁻¹b, x) dl_b dν(b). -/
structure IsDisintegration (J : Matrix ι ι A) (l : skewAdjoint A → Measure (ι → A)) where
  /-- For continuous f ≥ 0 of compact support, b ↦ ∫ f d`l b` is continuous on the skew elements and
  finite. -/
  continuous_and_lt_top {f : (ι → A) → NNReal} : Continuous f → HasCompactSupport f →
      Continuous (∫⁻ x : ι → A, f x ∂l ·) ∧ ∀ b : skewAdjoint A, ∫⁻ x : ι → A, f x ∂l b < ∞
  /-- For measurable f, the integral of f(x̄ᵀJx, x) against μ is the integral over skew b, against
  ν, of the integral of f(δ⁻¹b, x) against `l b`. -/
  lintegral_eq (f : A × (ι → A) → ℝ≥0∞) : Measurable f →
      ∫⁻ x : ι → A, f (star x ⬝ᵥ J *ᵥ x, x) ∂μ =
        ∫⁻ b : skewAdjoint A, ∫⁻ x : ι → A, f (skewUnit⁻¹.1 * b, x) ∂l b ∂skewMeasure

lemma modulus_star (x : A) : P.modulus (star x) = P.modulus x := (modulus_star_and_neg x).left

/-- A matrix T over a place A whose determinant d satisfies d̄d = 1 preserves the volume of A^ι. -/
lemma measurePreserving_mulVec (T : Matrix ι ι A) (h_det_norm : star T.det * T.det = 1) :
    MeasurePreserving (T *ᵥ ·) := by
  have h_sq : P.modulus T.det ^ 2 = 1 ^ 2 := by
    simpa [modulus_star, sq] using congrArg P.modulus h_det_norm
  have h_md : P.modulus T.det = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h_sq
  refine ⟨by fun_prop, ?_⟩
  simp [map_mulVec_volume ι T (.of_mul_eq_one_right _ h_det_norm), h_md]

variable {T b μ}

@[simp]
lemma modulus_inv (u : Aˣ) : P.modulus ↑u⁻¹ = (P.modulus u)⁻¹ :=
  ENNReal.eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

@[simp]
lemma modulus_ne_zero_and_ne_top (u : Aˣ) : P.modulus u ≠ 0 ∧ P.modulus u ≠ ∞ :=
  isUnit_iff.1 (u.isUnit.map P.modulus)

lemma modulus_ne_zero (u : Aˣ) : P.modulus u ≠ 0 := (modulus_ne_zero_and_ne_top u).left

lemma modulus_ne_top (u : Aˣ) : P.modulus u ≠ ∞ := (modulus_ne_zero_and_ne_top u).right

/-- Multiplication by a unit u maps the volume of A to (`modulus` u)⁻¹ times itself. -/
lemma map_mul_volume (u : Aˣ) : volume.map (u.val * ·) = (P.modulus u)⁻¹ • volume := by
  -- The case of a `1 × 1` matrix in `map_mulVec_volume`, carried along `(Fin 1 → A) ≃ A`.
  let e : (Fin 1 → A) ≃ᵐ A := MeasurableEquiv.funUnique (Fin 1) A
  have h_eval : MeasurePreserving e := volume_preserving_funUnique (Fin 1) A
  have h_det : MeasurePreserving (!![u.val] *ᵥ ·) volume ((P.modulus u)⁻¹ • volume) :=
    ⟨by fun_prop, by simpa using P.map_mulVec_volume (Fin 1) !![u.val] (by simp)⟩
  have h_conj : (u.val * ·) = e ∘ (!![u.val] *ᵥ ·) ∘ e.symm :=
    funext fun x ↦ by simp [e, dotProduct]
  rw [h_conj]
  exact ((h_eval.smul_measure _).comp (h_det.comp (h_eval.symm e))).map_eq

@[simp]
lemma star_skewUnit_inv : star P.skewUnit⁻¹.val = -P.skewUnit⁻¹.val := by
  have h_star : star P.skewUnit = -P.skewUnit := Units.ext star_skewUnit
  rw [← coe_star_inv, h_star, _root_.inv_neg, Units.val_neg]

/-- For a place `A` (a locally compact star ring carrying a Haar measure ν = `skewMeasure` on its
skew elements and a modulus `modulus` describing how matrices scale volume), multiplication β ↦ uβ
by a hermitian unit `u` maps ν to (`modulus` u)^(-1/2) times ν. -/
lemma map_skewMeasure_hermitianMul (hu : star u.val = u) :
    skewMeasure.map (hermitianMul u.val hu) = P.modulus u ^ (-(1 / 2) : ℝ) • skewMeasure := by
  -- The chart `split` of `A` by two skew coordinates turns multiplication by `u` into `mul × mul`.
  -- So `mul × mul` scales `ν × ν` by `(modulus u)⁻¹`; evaluate on a square `S ×ˢ S`.
  let mul : skewAdjoint A → skewAdjoint A := hermitianMul u.val hu
  let split (p : skewAdjoint A × skewAdjoint A) : A := P.element * P.skewUnit⁻¹.val * p.1 + p.2
  have h_mul : Measurable mul := by fun_prop
  have h_split : MeasurePreserving split (skewMeasure.prod skewMeasure) := measurePreserving_split
  have h_fst (p : skewAdjoint A × skewAdjoint A) :
      P.skewUnit.val * (split p + star (split p)) = p.1 := by
    simp only [split, star_add, star_mul', star_skewUnit_inv, skewAdjoint.star_val_eq]
    linear_combination p.1.val * (Units.mul_inv P.skewUnit * (P.element + star P.element) +
      P.element_add_star)
  have h_inj : Injective split := fun a b hab ↦ by
    have h_eq : a.1 = b.1 := Subtype.ext (by rw [← h_fst, ← h_fst, hab])
    exact Prod.ext h_eq (by simpa [split, h_eq] using hab)
  have h_comm : split ∘ Prod.map mul mul = (u.val * ·) ∘ split :=
    funext fun p ↦ by simp [split, mul, mul_add, mul_left_comm]
  have h_prod : (skewMeasure.map mul).prod (skewMeasure.map mul) =
      (P.modulus u)⁻¹ • skewMeasure.prod skewMeasure := by
    refine (h_split.measurable.measurableEmbedding h_inj).map_injective ?_
    calc ((skewMeasure.map mul).prod (skewMeasure.map mul)).map split
        = (skewMeasure.prod skewMeasure).map (split ∘ Prod.map mul mul) := by
          rw [map_prod_map _ _ h_mul h_mul, Measure.map_map h_split.measurable (by fun_prop)]
      _ = volume.map (u.val * ·) := by
          rw [h_comm, ← Measure.map_map (by fun_prop) h_split.measurable, h_split.map_eq]
      _ = ((P.modulus u)⁻¹ • skewMeasure.prod skewMeasure).map split := by
          rw [map_mul_volume, (h_split.smul_measure _).map_eq]
  refine Measure.ext fun S _ ↦ (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  calc skewMeasure.map mul S ^ 2 = (P.modulus u)⁻¹ * skewMeasure S ^ 2 := by
        rw [sq, ← prod_prod, h_prod, Measure.smul_apply, prod_prod, _root_.smul_eq_mul, sq]
    _ = (P.modulus u ^ (-(1 / 2) : ℝ) • skewMeasure) S ^ 2 := by
        simp [mul_pow, ← rpow_mul_natCast, rpow_neg_one]

/-- For a hermitian unit u, the map β ↦ skew part of τuβ (τ the trace-one element of the place, skew
part of x being x − x̄), which equals β ↦ uβ, maps the measure ν on the skew elements to (`modulus`
u)^(-1/2) times ν. -/
lemma map_skewMeasure_mul_unit (hu : star u.val = u) :
    skewMeasure.map (fun β : skewAdjoint A ↦ skewPart (P.element * u * β.val)) =
      (P.modulus u ^ (2⁻¹ : ℝ))⁻¹ • skewMeasure := by
  have h_skewPart (β : skewAdjoint A) :
      skewPart (P.element * u * β.val) = hermitianMul u.val hu β := by
    refine Subtype.ext ?_
    calc P.element * u * β.val - star (P.element * u * β.val) = (P.element + star P.element) *
           (u * β.val) := by
          rw [star_mul', star_mul', hu, skewAdjoint.star_val_eq]
          ring
      _ = u * β.val := by rw [element_add_star, one_mul]
  rw [funext h_skewPart, map_skewMeasure_hermitianMul u hu, rpow_neg, one_div]

/-! ### Properties of the chart and of disintegrations -/

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] (u : Aˣ) {T : Matrix ι ι A} {b : skewAdjoint A}
  {μ : Measure (ι → A)} {κ : Type} [Fintype κ]

@[fun_prop]
lemma measurable_flatChart :
    Measurable fun p : skewAdjoint A × (A × (ι → A)) × skewAdjoint A ↦ flatChart T p.1 p.2 := by
  fun_prop [flatChart]

/-- The skew element δΓ of a hermitian element Γ. The default proof of star Γ = Γ applies when Γ
is a diagonal entry of a matrix of class `IsHermitianUnit` (hermitian and invertible). -/
@[simps] def skewUnitMul (Γ : A)
    (hΓ : star Γ = Γ := by apply IsHermitian.apply IsHermitianUnit.conjTranspose_eq) :
      skewAdjoint A :=
  ⟨P.skewUnit * Γ, by simp [skewAdjoint, star_skewUnit, hΓ]⟩

/-- For a place `A` with skew unit δ (`skewUnit`) and trace-one element τ, let `T` be a hermitian
ι×ι matrix, `b` a skew-adjoint element, and h the hermitian form whose Gram matrix `planeSumGram T`
is a hyperbolic plane (e, e') plus `T`. For p = ((t, w), a) with t a unit, w : ι → A and a
skew-adjoint, the flat-chart point x = (t̄⁻¹τ(δ⁻¹b − h(w, w)) + ta)e + te' + w (`flatChart T b p`)
satisfies h(x, x) = star x ⬝ᵥ `planeSumGram T` *ᵥ x = δ⁻¹b, that is, x lies on the quadric of b. -/
lemma form_flatChart (hT : Tᴴ = T) {p : (A × (ι → A)) × skewAdjoint A} (hp : IsUnit p.1.1) :
    star (flatChart T b p) ⬝ᵥ planeSumGram T *ᵥ flatChart T b p = skewUnit⁻¹.val * b := by
  obtain ⟨⟨t, w⟩, a⟩ := p
  let q : A := star w ⬝ᵥ T *ᵥ w
  -- The skew term `t a t̄` cancels against its conjugate, and `τ + star τ = 1`.
  suffices ((star t)⁻¹ʳ * P.element * (skewUnit⁻¹.val * b - q) + t * a) * star t +
      t * (t⁻¹ʳ * star P.element * (skewUnit⁻¹.val * b - q) - star t * a) + q = skewUnit⁻¹.val * b
        by
    simpa [flatChart, fromBlocks_mulVec, star_sumElim, inverse_star,
      star_dotProduct_mulVec_comm hT w w,
      ← sub_eq_add_neg]
  linear_combination (skewUnit⁻¹.val * b - q) * (P.element * inverse_mul_cancel (star t) hp.star +
    star P.element * inverse_mul_cancel t hp + P.element_add_star)

/-- Let ν be the Haar measure on the skew elements, δ the skew unit and τ the element of trace one.
Let S be a set of skew elements and u a unit. Suppose that for any two pairs p, q in S × S, with
(β, β') = p − q, the element u(τδ⁻¹β + β') lies in C. If vol(C) / `modulus` u ≤ x², then
ν(S) ≤ x. -/
lemma skewMeasure_le_of_sub_mem {S : Set (skewAdjoint A)} {C : Set A} {x : ℝ≥0∞}
    (h_sub : ∀ p ∈ S ×ˢ S, ∀ q ∈ S ×ˢ S,
      u * (P.element * skewUnit⁻¹.val * ((p - q).1 : A) + ((p - q).2 : A)) ∈ C)
    (h_vol : (P.modulus u)⁻¹ * volume C ≤ x ^ 2) : skewMeasure S ≤ x := by
  -- A translate of `S ×ˢ S` lies in the preimage of `C` under `F`, the chart of
  -- `measurePreserving_split` followed by multiplication by `u`.
  let F (p : skewAdjoint A × skewAdjoint A) : A := u.val * (P.element * skewUnit⁻¹.val * p.1 + p.2)
  have hF : MeasurePreserving F (skewMeasure.prod skewMeasure) ((P.modulus u)⁻¹ • volume) :=
    .comp ⟨by fun_prop, map_mul_volume u⟩ measurePreserving_split
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, sq, ← prod_prod]
  calc skewMeasure.prod skewMeasure (S ×ˢ S) ≤ skewMeasure.prod skewMeasure (F ⁻¹' C) :=
        measure_le_of_sub_mem fun p hp ↦ ⟨p, fun q hq ↦ h_sub q hq p hp⟩
    _ ≤ x ^ 2 := (hF.measure_preimage_le C).trans h_vol

/-- The measures of a disintegration along the form with matrix T are finite on compact sets. -/
lemma IsDisintegration.isFiniteMeasureOnCompacts {l : skewAdjoint A → Measure (ι → A)}
    (hl : IsDisintegration μ T l) (b : skewAdjoint A) : IsFiniteMeasureOnCompacts (l b) := by
  refine ⟨fun K hK ↦ ?_⟩
  -- A continuous `f ≥ 0` of compact support that is one on `K` bounds the measure of `K`.
  obtain ⟨f, hf_one, -, hf_supp, -⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  calc l b K ≤ ∫⁻ x, (f x).toNNReal ∂l b :=
        meas_le_lintegral₀ (by fun_prop) fun x hx ↦ by simp [hf_one hx]
    _ < ∞ := (hl.continuous_and_lt_top (by fun_prop) (hf_supp.comp_left Real.toNNReal_zero)).right b

/-- Two disintegrations l, l' of the same measure μ along the form h(x, x) = x̄ᵀTx agree at every
skew element b. Here `IsDisintegration` requires two things: that ∫ f dl_b be finite and continuous
in b for continuous compactly supported f ≥ 0, and that ∫ f(h(x, x), x) dμ = ∬ f(δ⁻¹b, x) dl_b dν(b)
for measurable f. The continuity in b is why equality holds at every b rather than only almost
everywhere. -/
lemma IsDisintegration.unique {l l' : skewAdjoint A → Measure (ι → A)}
    (hl : IsDisintegration μ T l) (hl' : IsDisintegration μ T l') : l b = l' b := by
  classical
  -- Test against `f ≥ 0` continuous of compact support. The functions `b ↦ ∫⁻ f ∂l b` and
  -- `b ↦ ∫⁻ f ∂l' b` are continuous and have the same integral over every measurable set.
  have h_fin : IsFiniteMeasureOnCompacts (l b) := hl.isFiniteMeasureOnCompacts b
  have h_fin' : IsFiniteMeasureOnCompacts (l' b) := hl'.isFiniteMeasureOnCompacts b
  refine ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦ ?_
  obtain ⟨h_cont, -⟩ := hl.continuous_and_lt_top f.continuous f.hasCompactSupport
  obtain ⟨h_cont', -⟩ := hl'.continuous_and_lt_top f.continuous f.hasCompactSupport
  have h_setLIntegral : ∀ S : Set (skewAdjoint A), MeasurableSet S → skewMeasure S < ∞ →
      ∫⁻ β in S, ∫⁻ x, f x ∂l β ∂skewMeasure = ∫⁻ β in S, ∫⁻ x, f x ∂l' β ∂skewMeasure := by
    rintro _ ⟨s, hs, rfl⟩ -
    -- Both sides equal `∫⁻ x, Φ (h(x, x), x) ∂μ`.
    let Φ (p : A × (ι → A)) : ℝ≥0∞ := f p.2 * s.indicator 1 (skewUnit.1 * p.1)
    have hΦ : Measurable Φ := by fun_prop (disch := assumption)
    have h_both : ∫⁻ β : skewAdjoint A, (∫⁻ x, f x ∂l β) * s.indicator 1 β.val ∂skewMeasure =
        ∫⁻ β : skewAdjoint A, (∫⁻ x, f x ∂l' β) * s.indicator 1 β.val ∂skewMeasure := by
      simpa (disch := fun_prop) [Φ, lintegral_mul_const] using
        (hl.lintegral_eq Φ hΦ).symm.trans (hl'.lintegral_eq Φ hΦ)
    simpa [indicator, ← lintegral_indicator (measurable_subtype_coe hs)] using h_both
  have h_eq : (∫⁻ x, f x ∂l ·) = (∫⁻ x, f x ∂l' ·) :=
    eq_of_ae_eq (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite h_cont.measurable
      h_cont'.measurable h_setLIntegral) h_cont h_cont'
  have h_toReal (m : Measure (ι → A)) : ∫ x, (f x : ℝ) ∂m = (∫⁻ x, f x ∂m).toReal :=
    (f.toBoundedContinuousFunction.toReal_lintegral_coe_eq_integral m).symm
  rw [h_toReal, h_toReal, congrFun h_eq b]

/-- Let l disintegrate μ along the form with matrix T: measurable f satisfy ∫ f(x̄ᵀTx, x) dμ = ∬
f(δ⁻¹b, x) dl_b dν(b), and ∫ f dl_b is finite and continuous in b for continuous compactly
supported f ≥ 0. If M has a left inverse L and pulls the form J back to T, then the images of l_b
under M disintegrate the image of μ along J. -/
lemma IsDisintegration.map [DecidableEq ι] {l : skewAdjoint A → Measure (ι → A)} {M : Matrix κ ι A}
    {J : Matrix κ κ A} {L : Matrix ι κ A} (hl : IsDisintegration μ T l) (hJ : Mᴴ * J * M = T)
    (hL : L * M = 1) :
    IsDisintegration (μ.map (M *ᵥ ·)) J fun b : skewAdjoint A ↦ (l b).map (M *ᵥ ·) := by
  -- `M *ᵥ ·` has the continuous left inverse `L *ᵥ ·`, so it is a closed embedding.
  have h_emb : Topology.IsClosedEmbedding (M *ᵥ ·) :=
    LeftInverse.isClosedEmbedding (f := (L *ᵥ ·)) (fun x ↦ by simp [hL]) (by fun_prop) (by fun_prop)
  have h_form (x : ι → A) : star (M *ᵥ x) ⬝ᵥ J *ᵥ M *ᵥ x = star x ⬝ᵥ T *ᵥ x := by
    simp [star_mulVec_dotProduct, ← Matrix.mul_assoc, hJ]
  refine ⟨fun {f} hf hf_supp ↦ ?_, fun f hf ↦ ?_⟩ <;>
    simp only [h_emb.measurableEmbedding.lintegral_map, h_form]
  · exact hl.continuous_and_lt_top (by fun_prop) (hf_supp.comp_isClosedEmbedding h_emb)
  · exact hl.lintegral_eq (f ∘ Prod.map id (M *ᵥ ·)) (by fun_prop)

/-- Let `T` be any square matrix over `A` (not assumed hermitian), ν the Haar measure `skewMeasure`
on the skew elements, and `K` a compact subset of `Fin 2 ⊕ ι → A`. Let h be the form with Gram
matrix `planeSumGram T` (a hyperbolic plane e, e' plus T), and consider the flat chart
`flatChart T b` ((t, w), a) ↦ (t̄⁻¹τ(δ⁻¹b − h(w, w)) + ta)e + te' + w, where t̄⁻¹ is zero if t̄ is
not a unit. Then the supremum over skew `b` of the ν-measure of the fibre {a | flatChart T b ((t,
w), a) ∈ K} has finite lower integral over (t, w) ∈ A × (ι → A). -/
lemma lintegral_iSup_fibre_lt_top {K : Set (Fin 2 ⊕ ι → A)} (hK : IsCompact K) :
    ∫⁻ p : A × (ι → A), ⨆ b : skewAdjoint A,
      skewMeasure {a : skewAdjoint A | flatChart T b (p, a) ∈ K} < ∞ := by
  -- For a unit `t`, the fibre over `p = (t, w)` has measure `≤ ‖g t * √N‖` by
  -- `skewMeasure_le_of_sub_mem`, uniformly in `b`, and it is empty unless `p` lies in the
  -- compact `K₁ ×ˢ K₂`.
  obtain ⟨g, hg_int, hg⟩ : ∃ g : A → ℝ, LocallyIntegrable g volume ∧
      ∀ u : Aˣ, (P.modulus u)⁻¹ ≤ ‖g u‖ₑ ^ 2 := P.exists_locallyIntegrable_bound
  -- `C` holds the values `t (τ skewUnit⁻¹ β + β')` for differences `β`, `β'` of points of a fibre.
  let C : Set A :=
    (fun ((x₁, x₂), (y₁, y₂)) ↦ P.element * skewUnit⁻¹.val * (x₁ (inl 0) - y₁ (inl 0)) +
      (x₂ (inl 0) - y₂ (inl 0))) '' (K ×ˢ K) ×ˢ K ×ˢ K
  have hC : IsCompact C := ((hK.prod hK).prod (hK.prod hK)).image_of_continuous _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, volume C < N := ENNReal.exists_nat_gt hC.measure_ne_top
  let K₁ : Set A := (· (inl 1)) '' K
  let K₂ : Set (ι → A) := (· ∘ inr) '' K
  have h_int : IntegrableOn (fun p : A × (ι → A) ↦ g p.1 * √N) (K₁ ×ˢ K₂) :=
    ((hg_int.integrableOn_isCompact (hK.image_of_continuous _)).mul_prod
      (integrableOn_const (hK.image_of_continuous _).measure_ne_top)).mono_measure
        (prod_restrict K₁ K₂).ge
  suffices h_bound : ∀ᵐ p : A × (ι → A), ⨆ b, skewMeasure {a | flatChart T b (p, a) ∈ K} ≤
      (K₁ ×ˢ K₂).indicator (fun p ↦ ‖g p.1 * √N‖ₑ) p from
    calc _ ≤ ∫⁻ p in K₁ ×ˢ K₂, ‖g p.1 * √N‖ₑ :=
          (lintegral_mono_ae h_bound).trans (lintegral_indicator_le _ _)
      _ < ∞ := h_int.hasFiniteIntegral
  filter_upwards [quasiMeasurePreserving_fst.ae ae_isUnit] with p hp
  refine iSup_le fun b ↦ ?_
  let x (a : skewAdjoint A) : Fin 2 ⊕ ι → A := flatChart T b (p, a)
  by_cases hpK : p ∈ K₁ ×ˢ K₂
  · have h_vol : (P.modulus hp.unit)⁻¹ * volume C ≤ ‖g p.1 * √N‖ₑ ^ 2 := by
      simpa [mul_pow, ← enorm_pow] using mul_le_mul' (hg hp.unit) hN.le
    rw [indicator_of_mem hpK]
    refine skewMeasure_le_of_sub_mem hp.unit (fun a ha a' ha' ↦ ?_) h_vol
    -- The first coordinate of the chart point is affine in `a`, with slope `p.1`.
    refine ⟨((x a.1, x a.2), (x a'.1, x a'.2)), ⟨ha, ha'⟩, ?_⟩
    simp [x, flatChart, mul_sub, mul_add, mul_left_comm]
  · have h_empty : {a | x a ∈ K} = ∅ := by
      refine eq_empty_of_forall_notMem fun a ha ↦ hpK ⟨⟨x a, ha, ?_⟩, ⟨x a, ha, ?_⟩⟩ <;>
        simp [x, flatChart]
    simp [x, h_empty]

/-- Let T be hermitian, t a unit, w a vector and h the form of `planeSumGram T`. The integral over
s of f(h(x, x), x) at x = (s, t, w) is the double integral over skew b, a of f(δ⁻¹b, x) at the
chart point x of ((t, w), a) on the quadric of b. -/
lemma lintegral_form_eq_lintegral_flatChart (hT : Tᴴ = T)
    {f : A × (Fin 2 ⊕ ι → A) → ℝ≥0∞} (hf : Measurable f) (t : Aˣ) (w : ι → A) :
    ∫⁻ s : A, f (star (![s, t.val] ⊕ᵥ w) ⬝ᵥ planeSumGram T *ᵥ (![s, t.val] ⊕ᵥ w),
        ![s, t.val] ⊕ᵥ w) =
      ∫⁻ b : skewAdjoint A, ∫⁻ a : skewAdjoint A,
        f (skewUnit⁻¹.val * b, flatChart T b ((t.val, w), a)) ∂skewMeasure ∂skewMeasure := by
  -- Substitute `s b a = (star t)⁻¹ * (τ δ⁻¹ b + a - shift)`, with `shift = τ h(w, w)`, and scale
  -- `a` by `t t̄`; then `(s, t, w)` is the chart point.
  let G (s : A) : ℝ≥0∞ :=
    f (star (![s, t.val] ⊕ᵥ w) ⬝ᵥ planeSumGram T *ᵥ (![s, t.val] ⊕ᵥ w), ![s, t.val] ⊕ᵥ w)
  let starInv : Aˣ := star t⁻¹
  let shift : A := P.element * star w ⬝ᵥ T *ᵥ w
  let s (b a : skewAdjoint A) : A := starInv * (P.element * skewUnit⁻¹.1 * b + a - shift)
  let scale (a : skewAdjoint A) : skewAdjoint A := hermitianMul ↑(t * star t) (star_mul_star ..) a
  have h_point (b a : skewAdjoint A) : ![s b (scale a), t] ⊕ᵥ w = flatChart T b ((t, w), a) := by
    have h_coord : s b (scale a) =
        (star t.val)⁻¹ʳ * element * (skewUnit⁻¹.val * b - star w ⬝ᵥ T *ᵥ w) + t * a := by
      simp only [s, starInv, shift, scale, ← coe_star, inverse_unit, star_inv, val_mul]
      linear_combination t * a * Units.inv_mul (star t)
    rw [h_coord, flatChart]
  have h_scale : skewMeasure.map scale = (P.modulus ↑(t * star t) ^ (2⁻¹ : ℝ))⁻¹ • skewMeasure := by
    rw [map_skewMeasure_hermitianMul, rpow_neg, one_div]
  -- The Jacobian of the substitution is `modulus (star t)⁻¹ * modulus (t t̄) ^ (1 / 2) = 1`.
  have h_jac : P.modulus starInv * P.modulus (t * star t).1 ^ (2⁻¹ : ℝ) = 1 := by
    simp [starInv, ← sq, ← rpow_natCast_mul, ENNReal.inv_mul_cancel]
  calc ∫⁻ y, G y = P.modulus starInv * ∫⁻ y, G (starInv * (y - shift)) := by
        rw [lintegral_eq_mul_lintegral_map (map_mul_volume starInv) (by simp) (by simp),
          lintegral_map (by fun_prop) (by fun_prop), ← lintegral_sub_right_eq_self _ shift]
    _ = P.modulus starInv * ∫⁻ a, ∫⁻ b, G (s b a) ∂skewMeasure ∂skewMeasure := by
      rw [← measurePreserving_split.lintegral_comp (by fun_prop),
        lintegral_prod_symm _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ b, G (s b (scale a)) ∂skewMeasure ∂skewMeasure := by
      rw [lintegral_eq_mul_lintegral_map h_scale (by simp) (by simp [mul_eq_top]), ← mul_assoc,
        h_jac, one_mul, lintegral_map (by fun_prop) (by fun_prop)]
    _ = ∫⁻ b, ∫⁻ a, G (s b (scale a)) ∂skewMeasure ∂skewMeasure :=
      lintegral_lintegral_swap (by fun_prop)
    _ = _ := by simp only [G, h_point, form_flatChart hT, t.isUnit]

/-- For T hermitian, f ≥ 0 continuous of compact support and a base point p = (t, w) with t a
unit, the integral of f over the fibre of the flat chart at p is continuous in b. -/
lemma continuous_lintegral_flatChart (hT : Tᴴ = T) {f : (Fin 2 ⊕ ι → A) → NNReal}
    (hf : Continuous f) (hf_supp : HasCompactSupport f) {p : A × (ι → A)} (hp : IsUnit p.1) :
    Continuous fun b : skewAdjoint A ↦
      ∫⁻ a : skewAdjoint A, f (flatChart T b (p, a)) ∂skewMeasure := by
  -- The coordinate `a` is recovered from the chart point by `π`, free of `b`, so it stays in
  -- the compact set `π '' tsupport f`.
  let π (x : Fin 2 ⊕ ι → A) : skewAdjoint A := skewPart (star P.element * p.1⁻¹ʳ * x (inl 0))
  have hπ (b a : skewAdjoint A) : π (flatChart T b (p, a)) = a := by
    let q : A := star p.2 ⬝ᵥ T *ᵥ p.2
    have h_inv : p.1⁻¹ʳ * p.1 = 1 := inverse_mul_cancel p.1 hp
    -- With `s` the first coordinate, expand `τ̄ t⁻¹ s - τ t̄⁻¹ s̄`: the hermitian terms cancel, and
    -- `(τ̄ + τ) a = a` remains.
    suffices star P.element * p.1⁻¹ʳ * (star p.1⁻¹ʳ * element * (skewUnit⁻¹.val * b - q) + p.1 * a)
      -
        P.element * star p.1⁻¹ʳ * (p.1⁻¹ʳ * star P.element * (skewUnit⁻¹.val * b - q) - star p.1 *
          a) = a by
      simpa [Subtype.ext_iff, π, flatChart, inverse_star, star_dotProduct_mulVec_comm hT p.2 p.2,
        ← sub_eq_add_neg]
    have h_inv_star : star p.1⁻¹ʳ * star p.1 = 1 := by rw [← star_mul', h_inv, star_one]
    linear_combination a.val * (star P.element * h_inv + P.element * h_inv_star +
      P.element_add_star)
  have h_chart : Continuous fun q : skewAdjoint A × skewAdjoint A ↦ flatChart T q.1 (p, q.2) := by
    simp only [flatChart, continuous_pi_iff, Sum.forall, elim_inl, elim_inr]
    exact ⟨by fun_prop, by fun_prop⟩
  exact continuous_lintegral_of_compact_support (hf_supp.image_of_continuous π) (hf.comp h_chart)
    fun b a h_ne ↦ ⟨flatChart T b (p, a), subset_closure h_ne, hπ b a⟩

/-- For f ≥ 0 continuous of compact support, the integral of f over the fibre of the flat chart at
p = (t, w) is at most sup f times the supremum over b of the ν-measures of the sets
{a | the chart point at (p, a) for b lies in the topological support of f}. -/
lemma lintegral_flatChart_le {f : (Fin 2 ⊕ ι → A) → NNReal} (hf : Continuous f)
    (hf_supp : HasCompactSupport f) (b : skewAdjoint A) (p : A × (ι → A)) :
    ∫⁻ a : skewAdjoint A, f (flatChart T b (p, a)) ∂skewMeasure ≤ ofNNReal (iSup f) *
      ⨆ β : skewAdjoint A, skewMeasure {a : skewAdjoint A | flatChart T β (p, a) ∈ tsupport f} := by
  let S (β : skewAdjoint A) : Set (skewAdjoint A) := {a | flatChart T β (p, a) ∈ tsupport f}
  calc _ = ∫⁻ a in S b, f (flatChart T b (p, a)) ∂skewMeasure := Eq.symm <|
        setLIntegral_eq_of_support_subset fun a ha ↦ subset_closure (by simpa using ha)
    _ ≤ ∫⁻ _ in S b, ofNNReal (iSup f) ∂skewMeasure :=
        lintegral_mono fun a ↦ coe_le_coe.2 (le_ciSup (hf_supp.isCompact_range hf).bddAbove _)
    _ ≤ ofNNReal (iSup f) * ⨆ β, skewMeasure (S β) := by
        grw [setLIntegral_const, ← le_iSup _ b]

/-- Let `T` be hermitian and let h be the form with Gram matrix `planeSumGram T` (a hyperbolic plane
plus T). The measures `quadricMeasure T b` are the images of dt dw dν(a) under the flat chart. They
disintegrate `volume` along h(v, v): they are the fibre measures on h(v, v) = δ⁻¹b for skew b, with
base measure ν. -/
lemma isDisintegration_quadricMeasure (hT : Tᴴ = T) :
    IsDisintegration volume (planeSumGram T) (quadricMeasure T) := by
  -- Both properties are checked in the coordinates `((t, w), a)` of the chart, where `t` may be
  -- taken to be a unit.
  have h_unit : ∀ᵐ p : A × (ι → A), IsUnit p.1 := quasiMeasurePreserving_fst.ae ae_isUnit
  refine ⟨fun {f} hf hf_supp ↦ ?_, fun f hf ↦ ?_⟩ <;>
    simp (disch := fun_prop) only [quadricMeasure, lintegral_map, lintegral_prod]
  · -- Finiteness and continuity in `b`: the integrals over the fibres have a majorant free of `b`.
    let bound (p : A × (ι → A)) : ℝ≥0∞ := ofNNReal (iSup f) *
      ⨆ β : skewAdjoint A, skewMeasure {a | flatChart T β (p, a) ∈ tsupport f}
    have h_fin : ∫⁻ p, bound p < ∞ := by
      simpa [bound, lintegral_const_mul'] using
        mul_lt_top coe_lt_top (lintegral_iSup_fibre_lt_top hf_supp)
    refine ⟨continuous_iff_continuousAt.2 fun b ↦ ?_,
      fun b ↦ (lintegral_mono (lintegral_flatChart_le hf hf_supp b)).trans_lt h_fin⟩
    have h_cont_fibre : ∀ᵐ p : A × (ι → A),
        ContinuousAt (fun β : skewAdjoint A ↦ ∫⁻ a, f (flatChart T β (p, a)) ∂skewMeasure) b :=
      h_unit.mono fun p hp ↦ (continuous_lintegral_flatChart hT hf hf_supp hp).continuousAt
    exact tendsto_lintegral_filter_of_dominated_convergence bound (.of_forall (by fun_prop))
      (.of_forall fun β ↦ .of_forall (lintegral_flatChart_le hf hf_supp β)) h_fin.ne h_cont_fibre
  · -- The disintegration formula, in coordinates `x = (s, t, w)`, for fixed `w` and unit `t`.
    let Φ (x : Fin 2 ⊕ ι → A) : ℝ≥0∞ := f (star x ⬝ᵥ planeSumGram T *ᵥ x, x)
    let fibre (b : skewAdjoint A) (p : A × (ι → A)) : ℝ≥0∞ :=
      ∫⁻ a, f (skewUnit⁻¹.val * b, flatChart T b (p, a)) ∂skewMeasure
    calc ∫⁻ x, Φ x = ∫⁻ r : A × A × (ι → A), Φ (![r.1, r.2.1] ⊕ᵥ r.2.2) :=
          (measurePreserving_pair_sumElim.lintegral_comp (by fun_prop)).symm
      _ = ∫⁻ p : A × (ι → A), ∫⁻ s : A, Φ (![s, p.1] ⊕ᵥ p.2) := lintegral_prod_symm' _ (by fun_prop)
      _ = ∫⁻ p, ∫⁻ b, fibre b p ∂skewMeasure := lintegral_congr_of_ae_imp h_unit fun p hp ↦
          lintegral_form_eq_lintegral_flatChart hT hf hp.unit p.2
      _ = ∫⁻ b, ∫⁻ p, fibre b p ∂volume ∂skewMeasure := lintegral_lintegral_swap (by fun_prop)

end Place

end New.Floors
