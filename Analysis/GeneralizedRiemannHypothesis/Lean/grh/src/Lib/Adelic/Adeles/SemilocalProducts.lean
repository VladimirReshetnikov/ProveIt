import Lib.SiegelWeil.Mass

/-!
# Products of completions at finite sets of places and approximation of adeles by elements of E

Let `S` be a finite set of finite places of the number field `E`. The ring `New.LocProd S` is the
product of the completions `E_w` for `w ∈ S`, and `O` is the product of their rings of integers. The
file relates `New.LocProd S` to the finite adeles through the projection `New.evalPlaces S` and the
extension by zero `New.adeleOfLocal S`. It computes the projection of Haar measure and the
generalized index of an element of `New.LocProd S`, and it bounds the zeta function of `O`. For a CM
field `E` and `S` stable under conjugation it defines the involution of `New.LocProd S`.

## Main definitions and results

* `New.exists_principal_near_of_mem_differentIdeal`: approximation of an adele by an element of `E`.
* `New.integralOff`, `New.locProd_O_eq_map_evalPlaces`, `New.map_evalPlaces_restrict_volume`: the
  adeles integral off `S`, and the effect of the projection `New.evalPlaces S` on the integral
  adeles `New.Ô E` and on Haar measure.
* `New.idealZeta_locProd_le`, `New.genIndex_eq_inv_prod_norm`, `New.sqrt_genIndex_le_prod_norm`: the
  zeta function of `O` and the generalized index.

Notions from other files:
* `𝔸f E`, `New.Ô E`: the finite adeles of `E` and the subring of those integral at every place.
* `New.LocField w`, `New.LocInt w`: the completion `E_w` at the finite place `w` and its integers.
* `New.genIndex a`: the inverse of the factor by which the unit `a` scales Haar measure, and `0` if
  `a` is not a unit.
* `Φ w`: the chosen complex embedding of `E` at the infinite place `w`, given by
  `New.PlaceEmbedding E`, which is part of `New.CMType E`.
* `New.HasPrimitiveRoot5040 E`: the CM field `E` contains a primitive `5040`-th root of unity.

## Relation to the literature

Known; see `Lib.Adelic.Adeles.Basic` for sources.
-/

noncomputable section

/-!
## Effective approximation of adeles by elements of E

`New.exists_principal_near_of_mem_differentIdeal`: every adele of the CM field `E` differs from an
element of `E` by an adele that is integral at the finite places and of explicitly bounded size at
the infinite ones. The bound comes from the covering radius of the dual of the lattice `𝓞 E`.
-/

section RationalNear

open NumberField New.Space

/-- Let `d ≠ 0` lie in the different of the CM field `E`, and let `f = Core.numInfPlaces E` be the
number of infinite places. For every adele `(z, y)` there is `a` in `E` such that `y - a` lies
in the ring `Ô E` of integral finite adeles and `‖z w - Φ w a‖ ≤ (2 * f) ^ 2 * ‖Φ w d‖` at all
infinite places `w`, where `Φ w` is the chosen complex embedding at `w`. -/
lemma New.exists_principal_near_of_mem_differentIdeal {E : Type} [Field E] [CMType E] {d : 𝓞 E}
    (hd : d ≠ 0) (hd_diff : d ∈ differentIdeal ℤ (𝓞 E)) (z : InfinitePlace E → ℂ) (y : 𝔸f E) :
    ∃ a : E,
      y - algebraMap E (𝔸f E) a ∈ Ô E ∧
      ∀ w : InfinitePlace E, ‖z w - Φ w a‖ ≤ (2 * Core.numInfPlaces E) ^ 2 * ‖Φ w d‖ := by
  obtain ⟨r, hr⟩ : ∃ r : E, y - algebraMap E (𝔸f E) r ∈ Ô E := exists_sub_mem_Ô y
  -- Approximate `u = (z - r) / d` by `2 a / d` with `a` in the lattice of `stdSpace E Unit`, that
  -- is, an integer of `E`; then `r + 2 a` is close to `z`.
  let u : EuclideanSpace ℂ (InfinitePlace E × Unit) := .toLp 2 fun (w, _) ↦ (z w - Φ w r) / Φ w d
  obtain ⟨a, ha, h_near⟩ : ∃ a ∈ (stdSpace E Unit).baseLattice,
      ‖u - (stdSpace E Unit).archCoords ((2 / d : E) • a)‖ ≤
        (2 * (Core.numInfPlaces E * Fintype.card Unit)) ^ 2 / (stdSpace E Unit).firstMinimum :=
    (stdSpace E Unit).exists_norm_sub_archCoords_le hd hd_diff u
  refine ⟨r + 2 * a (), ?_, fun w ↦ ?_⟩
  · rw [map_add, ← sub_sub]
    exact sub_mem hr (by simpa [vecAtPoint] using nsmul_mem ha 2 ())
  · -- This lattice has minimum at least `1`; read the bound at `w` and multiply by `‖Φ w d‖`.
    have h_min : 1 ≤ (stdSpace E Unit).firstMinimum := one_le_firstMinimum fun _ _ ↦ rfl
    grw [← h_min, ← PiLp.norm_apply_le _ (w, ())] at h_near
    have h_w : ‖(z w - Φ w r) / Φ w d - Φ w (2 / d * a ())‖ ≤ (2 * Core.numInfPlaces E) ^ 2 := by
      simpa [u, archCoords, vecAtPoint] using h_near
    simpa [div_mul_eq_mul_div, ← sub_div, hd, div_le_iff₀, sub_sub] using h_w

end RationalNear

namespace New

/-!
## Projection to finitely many places and extension by zero

For a finite set `P` of finite places, `New.evalPlaces P` sends a finite adele to its components in
the product `New.LocProd P` of the completions at `P`, and `New.adeleOfLocal P` extends such
components by zero. Both are continuous, `evalPlaces P ∘ adeleOfLocal P` is the identity
(`New.evalPlaces_adeleOfLocal`), and `adeleOfLocal P ∘ evalPlaces P` is multiplication by the
idempotent `New.idem P` (`New.adeleOfLocal_evalPlaces`).
-/

section LocalComponents

open RestrictedProduct

variable {E : Type} [Field E] [NumberField E] (P : Finset (FinPlace E))

/-- The ring homomorphism sending a finite adele to its components at the places of the finite
set `P`. -/
@[simps!]
noncomputable def evalPlaces : 𝔸f E →+* LocProd P := RingHom.pi fun w ↦ evalAt w.1

open scoped Classical in
/-- Extension by zero: the additive and multiplicative map from the product of the completions
`E_w`, `w ∈ P`, to the finite adeles, with component `0` outside `P`. -/
noncomputable def adeleOfLocal : LocProd P →ₙ+* 𝔸f E where
  toFun y :=
    inclusion _ _ (𝓖 := Filter.principal Pᶜ) (by simp)
      (RestrictedProduct.mk (fun w ↦ if h : w ∈ P then y ⟨w, h⟩ else 0) (by aesop))
  map_mul' x y := by
    congrm ⟨fun w ↦ ?_, _⟩
    by_cases h : w ∈ P <;> simp [h]
  map_zero' := by
    congrm ⟨fun w ↦ ?_, _⟩
    by_cases h : w ∈ P <;> simp [h]
  map_add' x y := by
    congrm ⟨fun w ↦ ?_, _⟩
    by_cases h : w ∈ P <;> simp [h]

open scoped Classical in
lemma adeleOfLocal_apply (y : LocProd P) (w : FinPlace E) :
    adeleOfLocal P y w = if h : w ∈ P then y ⟨w, h⟩ else 0 :=
  rfl

@[fun_prop]
lemma continuous_adeleOfLocal : Continuous (adeleOfLocal P) := by
  classical
  -- `adeleOfLocal P` factors through the restricted product for the principal filter of `Pᶜ`, which
  -- has the subspace topology of the product; there each component is a projection or `0`.
  have h_components : Continuous fun (y : LocProd P) (w : FinPlace E) ↦
      if h : w ∈ P then y ⟨w, h⟩ else 0 := continuous_pi fun w ↦ by split <;> fun_prop
  exact (continuous_inclusion (R := LocField) (by simp)).comp
    (continuous_rng_of_principal.2 h_components)

@[fun_prop]
lemma continuous_evalPlaces : Continuous (evalPlaces P) :=
  continuous_pi fun w ↦ continuous_evalAt w.val

@[simp]
lemma evalPlaces_adeleOfLocal (x : LocProd P) : evalPlaces P (adeleOfLocal P x) = x :=
  funext fun w ↦ dite_eq_left w.prop

/-- Projecting to the places in `P` and extending by zero is multiplication by `idem P`, the adele
with component `1` on `P` and `0` elsewhere. -/
lemma adeleOfLocal_evalPlaces (x : 𝔸f E) : adeleOfLocal P (evalPlaces P x) = idem P * x := by
  ext w
  by_cases hw : w ∈ P <;> simp [adeleOfLocal_apply, hw]

end LocalComponents

/-!
## Measure, zeta function and generalized index of the product of completions

Here `O` is the subring `New.SemilocalField.O` of `New.LocProd S`, the product of the rings of
integers; it is compact, open and of volume one. The units of `New.LocProd S` embed openly into
`New.LocProd S` (`IsOpenUnits`). For `S` stable under conjugation, `New.LocProd S` has a continuous
involution, and `O` satisfies `New.IsAdelic` under `New.HasPrimitiveRoot5040 E`: it is open,
compact, stable under `star` and a valuation pair, and it contains a skew unit and an element of
norm `-1`.
-/

section SemilocalPlace

open Filling NumberField FinitePlace MeasureTheory Valued Pi Pointwise SemilocalField Floors ENNReal
  Function Finset

variable {E : Type} [Field E] [NumberField E] (S : Finset (FinPlace E))

/-- The ring of finite adeles of `E` that are integral at every place outside `S`. -/
def integralOff : Subring (𝔸f E) := ⨅ w ∉ S, (LocInt w).toSubring.comap (evalAt w)

/-- The diagonal ring homomorphism from `E` to the product of the completions `E_w`, `w ∈ S`. -/
abbrev ratToPlaces : E →+* LocProd S := (evalPlaces S).comp (algebraMap E (𝔸f E))

/-- The ring of `S`-integers of `E`: the elements integral at every finite place outside `S`. -/
abbrev Filling.ratIntegralOff : Subring E := (integralOff S).comap (algebraMap E (𝔸f E))

/-- A finite adele lies in `integralOff S` if and only if its components at the places outside `S`
have valuation at most `1`. -/
lemma mem_integralOff {x : 𝔸f E} :
    x ∈ integralOff S ↔ ∀ w : FinPlace E, w ∉ S → v (x w) ≤ 1 := by
  simp [integralOff, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

lemma isOpen_integralOff : IsOpen (integralOff S : Set (𝔸f E)) :=
  AddSubgroup.isOpen_mono (H₁ := (Ô E).toAddSubgroup) (H₂ := (integralOff S).toAddSubgroup)
    (fun _ hx ↦ (mem_integralOff S).2 fun w _ ↦ mem_Ô.1 hx w) isOpen_Ô

lemma evalAt_adeleOfLocal_of_notMem {w : FinPlace E} (hw : w ∉ S) (x : LocProd S) :
    evalAt w (adeleOfLocal S x) = 0 := dite_eq_right hw

@[simp]
lemma adeleOfLocal_mem_integralOff (x : LocProd S) : adeleOfLocal S x ∈ integralOff S :=
  (mem_integralOff S).2 fun w hw ↦ by simp [adeleOfLocal_apply, hw]

/-- Extension by zero is linear over the finite adeles, which act on `LocProd S` through the
projection `evalPlaces S`. -/
lemma adeleOfLocal_evalPlaces_mul (a : LocProd S) (b : 𝔸f E) :
    adeleOfLocal S (evalPlaces S b * a) = b * adeleOfLocal S a := by
  rw [← evalPlaces_adeleOfLocal S a, ← map_mul, adeleOfLocal_evalPlaces, adeleOfLocal_evalPlaces,
    mul_left_comm]

/-- A finite adele is integral at all places if and only if its projection to the places in `S` lies
in the ring of integers `O` of `LocProd S` and it is integral outside `S`. -/
lemma mem_Ô_iff {x : 𝔸f E} :
    x ∈ Ô E ↔ evalPlaces S x ∈ (O : Subring (LocProd S)) ∧ x ∈ integralOff S := by
  rw [mem_O_locProd, mem_integralOff, mem_Ô]
  refine ⟨fun hx ↦ ⟨fun w ↦ hx w, fun w _ ↦ hx w⟩, fun ⟨h_in, h_off⟩ w ↦ ?_⟩
  by_cases hw : w ∈ S
  exacts [h_in ⟨w, hw⟩, h_off w hw]

/-- The ring of integers `O` of `LocProd S` is the projection of the ring `Ô E` of integral finite
adeles. -/
lemma locProd_O_eq_map_evalPlaces : (O : Subring (LocProd S)) = (Ô E).map (evalPlaces S) := by
  ext x
  refine ⟨fun hx ↦ ⟨adeleOfLocal S x, by simpa [mem_Ô_iff S] using hx,
    evalPlaces_adeleOfLocal S x⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact ((mem_Ô_iff S).1 hy).left

/-- A finite adele with its components in `S` removed is integral at all places if and only if the
adele is integral outside `S`. -/
lemma sub_adeleOfLocal_mem_iff {x : 𝔸f E} :
    x - adeleOfLocal S (evalPlaces S x) ∈ Ô E ↔ x ∈ integralOff S := by
  have h_in : evalPlaces S (x - adeleOfLocal S (evalPlaces S x)) = 0 := by simp
  rw [mem_Ô_iff S, h_in, and_iff_right (zero_mem _), sub_eq_add_neg]
  exact add_mem_cancel_right (neg_mem (adeleOfLocal_mem_integralOff S _))

instance : IsOpenUnits (LocProd S) := ⟨Units.isOpenEmbedding_val⟩

/-! ### Zeta function and measure -/

/-- For a number field `E` and a finite set `S` of finite places of `E`, `LocProd S` is the product
of the completions `E_w` over the places `w` in `S`. The ideal zeta sum `∑ [R : I]⁻¹ ^ μ` (valued in
`[0, ∞]`) over the ideals `I` of finite index is at most as large for the ring of integers `R = O`
of `LocProd S` as for the integral finite adeles `R = Ô E`. -/
lemma idealZeta_locProd_le (μ : ℕ) : idealZeta (O : Subring (LocProd S)) μ ≤ idealZeta (Ô E) μ := by
  -- Pulling back along the surjection `f : Ô E → R` is injective on ideals and keeps the index.
  let R : Subring (LocProd S) := O
  let f : Ô E →+* R := (evalPlaces S).restrict (Ô E) R fun x hx ↦ ((mem_Ô_iff S).1 hx).left
  have hf : Surjective f := fun ⟨x, hx⟩ ↦
    let ⟨y, hy, hyx⟩ := (locProd_O_eq_map_evalPlaces S).le hx
    ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have index_comap (I : Ideal R) : (I.comap f).cardQuot = I.cardQuot :=
    I.toAddSubgroup.index_comap_of_surjective (f := f.toAddMonoidHom) hf
  let pull : {I : Ideal R // I.cardQuot ≠ 0} → {I : Ideal (Ô E) // I.cardQuot ≠ 0} :=
    Subtype.map (.comap f) fun I hI ↦ (index_comap I).trans_ne hI
  calc idealZeta R μ
    _ = ∑' I : {I : Ideal R // I.cardQuot ≠ 0}, ((pull I).val.cardQuot : ℝ≥0∞)⁻¹ ^ μ :=
      tsum_congr fun I ↦ by simp [pull, index_comap]
    _ ≤ idealZeta (Ô E) μ := tsum_comp_le_tsum_of_injective
      (Subtype.map_injective _ (Ideal.comap_injective_of_surjective f hf))
      fun I ↦ (I.val.cardQuot : ℝ≥0∞)⁻¹ ^ μ

/-- The projection carries Haar measure on the adeles that are integral off `S` to `New.volÔ E`, the
mass of `New.Ô E`, times the Haar measure of `New.LocProd S` that gives `O` mass one. -/
lemma map_evalPlaces_restrict_volume :
    (volume.restrict (integralOff S : Set (𝔸f E))).map (evalPlaces S) =
      volÔ E • (volume : Measure (LocProd S)) := by
  -- Every point of `LocProd S` lifts to a translation preserving `integralOff S`, so the image
  -- measure is invariant; compare it with `volume` on `O`, whose preimage in `integralOff S` is
  -- `Ô E`.
  have lift : HasAddStableLifts (evalPlaces S).toAddMonoidHom (integralOff S : Set (𝔸f E)) :=
    fun y ↦ ⟨adeleOfLocal S y, by simp [add_mem_cancel_left, add_mem_cancel_right]⟩
  have preimage : evalPlaces S ⁻¹' (O : Subring (LocProd S)) ∩ integralOff S = Ô E :=
    Set.ext fun _ ↦ (mem_Ô_iff S).symm
  have h_map :
      volume ((O : Subring (LocProd S)) : Set (LocProd S)) •
          (volume.restrict (integralOff S : Set (𝔸f E))).map (evalPlaces S).toAddMonoidHom =
        volume (Ô E : Set (𝔸f E)) • (volume : Measure (LocProd S)).neg := by
    rw [← preimage]
    exact measure_smul_map_restrict_eq_smul_neg volume volume (by measurability)
      (isOpen_integralOff S).measurableSet lift isCompact_O.measurableSet
  -- `O` has volume one, and Haar measure on `LocProd S` is invariant under negation.
  simpa [volume_O] using h_map

/-- In the ring of integers `O` of `LocProd S`, the `r` with `a * r ∈ O` form a subgroup of finite
index: its index `denomIndex O a` is nonzero (an infinite index is `0`). -/
lemma denomIndex_ne_zero (a : LocProd S) : denomIndex (O : Subring (LocProd S)) a ≠ 0 :=
  isCompact_O.relIndex_ne_zero_add (isOpen_O.preimage (continuous_const_mul _))

/-- Let `a` in the completion at `w` have norm greater than `1`, and let `0 < t`. The level set of
the `x` with `√(‖x‖⁻¹ - 1) ≥ t`, that is with `0 < ‖x‖ ≤ (1 + t ^ 2)⁻¹`, has volume at most
`(1 + t ^ 2)⁻¹ * ‖a‖`. -/
lemma volume_setOf_le_sqrt_inv_norm_sub_one_le {w : FinPlace E} {a : LocField w} (ha : 1 < ‖a‖)
    {t : ℝ} (ht : 0 < t) :
    volume {x : LocField w | t ≤ ‖√(‖x‖⁻¹ - 1)‖} ≤ .ofReal ((1 + t ^ 2)⁻¹ * ‖a‖) := by
  -- `d` has norm between `(1 + t ^ 2) / ‖a‖` and `1 + t ^ 2`, and multiplication by `d` maps the
  -- level set into `LocInt w`.
  obtain ⟨d, hd, hd_lt, hd_inv⟩ :
      ∃ d : LocField w, d ≠ 0 ∧ ‖d‖ < 1 + t ^ 2 ∧ ‖d‖⁻¹ ≤ (1 + t ^ 2)⁻¹ * ‖a‖ := by
    obtain ⟨d, hd, hd_lt, -, hd_inv⟩ :=
      rescale_to_shell ha (by positivity : 0 < 1 + t ^ 2) (one_ne_zero' (LocField w))
    exact ⟨d, hd, by simpa using hd_lt, by simpa using hd_inv⟩
  let u : (LocField w)ˣ := Units.mk0 d hd
  have h_subset : {x : LocField w | t ≤ ‖√(‖x‖⁻¹ - 1)‖} ⊆ u⁻¹ • (LocInt w : Set (LocField w)) := by
    intro x hx
    have hx_sq : t ^ 2 ≤ ‖x‖⁻¹ - 1 := by simpa [abs_of_nonneg, Real.le_sqrt' ht] using hx
    have hd_le : ‖d‖ ≤ ‖x‖⁻¹ := by linarith
    have h_norm : ‖d * x‖ ≤ 1 := by grw [norm_mul, hd_le, inv_mul_le_one]
    exact Set.mem_inv_smul_set_iff.2 (toNormedField.norm_le_one_iff.1 h_norm)
  calc volume {x : LocField w | t ≤ ‖√(‖x‖⁻¹ - 1)‖}
    _ ≤ volume (u⁻¹ • (LocInt w : Set (LocField w))) := measure_mono h_subset
    _ = .ofReal (genIndex u.val) := by
      simp [← distribHaarChar_mul, coe_nnreal_eq, ← genIndex_eq_inv_distribHaarChar]
    _ = .ofReal ‖d‖⁻¹ := by rw [genIndex_eq_inv_norm, Units.val_mk0]
    _ ≤ .ofReal ((1 + t ^ 2)⁻¹ * ‖a‖) := ofReal_le_ofReal hd_inv

/-- The function `1 + √(‖x‖⁻¹ - 1)` is locally integrable on the completion at `w`; note that `√`
vanishes on negative numbers, so the root is zero for `‖x‖ ≥ 1`. -/
lemma locallyIntegrable_one_add_sqrt_inv_norm_sub_one (w : FinPlace E) :
    LocallyIntegrable fun x : LocField w ↦ 1 + √(‖x‖⁻¹ - 1) := by
  -- Layer cake formula: the volume of the set where `√(‖x‖⁻¹ - 1) ≥ t` is at most
  -- `(1 + t ^ 2)⁻¹ * ‖a‖`, which is integrable in `t`.
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm (LocField w)
  suffices h_int : Integrable fun x : LocField w ↦ √(‖x‖⁻¹ - 1) from
    (locallyIntegrable_const 1).add h_int.locallyIntegrable
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_norm _).2 ?_⟩
  calc ∫⁻ x : LocField w, .ofReal ‖√(‖x‖⁻¹ - 1)‖
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), volume {x : LocField w | t ≤ ‖√(‖x‖⁻¹ - 1)‖} :=
      lintegral_eq_lintegral_meas_le _ (.of_forall fun x ↦ norm_nonneg _) (by fun_prop)
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), .ofReal ((1 + t ^ 2)⁻¹ * ‖a‖) :=
      setLIntegral_mono' measurableSet_Ioi fun t ht ↦ volume_setOf_le_sqrt_inv_norm_sub_one_le ha ht
    _ < ∞ := (integrable_inv_one_add_sq.mul_const ‖a‖).restrict.lintegral_lt_top

/-! ### The generalized index and the product formula -/

/-- The generalized index `genIndex x` of `x` in the product of the completions at `S` (the inverse
of the factor by which `x` scales Haar measure) is the inverse of the product of the local norms of
`x`. Both sides are `0` if a component of `x` is zero. -/
lemma genIndex_eq_inv_prod_norm (x : LocProd S) : genIndex x = (∏ w : S, ‖x w‖)⁻¹ := by
  by_cases hx : IsUnit x
  · -- Both sides are the factor by which `u⁻¹` scales the volume of `∏ w, LocInt w`.
    obtain ⟨u, rfl⟩ := hx
    let B : ∀ w : S, Set (LocField w.val) := fun w ↦ LocInt w.val
    have h_scale : u⁻¹ • Set.univ.pi B = Set.univ.pi fun w : S ↦ MulEquiv.piUnits u⁻¹ w • B w :=
      Set.piMap_image_univ_pi (fun w x ↦ MulEquiv.piUnits u⁻¹ w • x) B
    calc genIndex u.val
      _ = (volume (u⁻¹ • Set.univ.pi B)).toReal := by
        simp [B, ← distribHaarChar_mul, volume_pi_pi, ← genIndex_eq_inv_distribHaarChar]
      _ = ∏ w : S, genIndex (MulEquiv.piUnits u w).val := by
        simp [h_scale, B, ← distribHaarChar_mul, volume_pi_pi, ← genIndex_eq_inv_distribHaarChar]
      _ = (∏ w : S, ‖u.val w‖)⁻¹ := (prod_congr rfl fun w _ ↦
        genIndex_eq_inv_norm (MulEquiv.piUnits u w)).trans (Finset.prod_inv_distrib _)
  · -- A non-unit has a zero component, and both sides vanish.
    obtain ⟨w, hw⟩ : ∃ w : S, x w = 0 := by simpa [Pi.isUnit_iff] using hx
    rw [genIndex.map_nonunit hx,
      prod_eq_zero (f := fun w : S ↦ ‖x w‖) (mem_univ w) (norm_eq_zero.2 hw), _root_.inv_zero]

/-- Let `y ≠ 0` be an `S`-integer of the totally complex field `E`. By the product formula, the
square root of its generalized index in `LocProd S` is at most `∏ v, ‖Φ v y‖`, the product over
the infinite places. -/
lemma sqrt_genIndex_le_prod_norm [IsTotallyComplex E] [PlaceEmbedding E] {y : E} (hy_ne : y ≠ 0)
    (hy_int : y ∈ ratIntegralOff S) :
    √(genIndex (ratToPlaces S y)) ≤ ∏ v : InfinitePlace E, ‖Φ v y‖ := by
  classical
  -- By the product formula, `|N y|⁻¹` is the product of `‖y‖` over all finite places, and the
  -- factors off `S` are at most `1`. So the index is at most `|N y| = ∏ v, ‖Φ v y‖ ^ 2`.
  let f (w : FinPlace E) : ℝ := ‖algebraMap E (𝔸f E) y w‖
  have hf_fin : HasFiniteMulSupport f :=
    (hasFiniteMulSupport hy_ne).preimage (f := equivHeightOneSpectrum.symm) (by simp)
  have h_index : genIndex (ratToPlaces S y) = (∏ w ∈ S, f w)⁻¹ :=
    (genIndex_eq_inv_prod_norm S _).trans (congrArg (·⁻¹) (S.prod_coe_sort f))
  have h_inv_le : |(Algebra.norm ℚ y : ℝ)|⁻¹ ≤ ∏ w ∈ S, f w :=
    calc |(Algebra.norm ℚ y : ℝ)|⁻¹
      _ = ∏ᶠ w : FinitePlace E, w y := mod_cast (prod_eq_inv_abs_norm hy_ne).symm
      _ = ∏ w ∈ S ∪ hf_fin.toFinset, f w :=
        (finprod_comp_equiv equivHeightOneSpectrum.symm).symm.trans
          (finprod_eq_prod_of_mulSupport_toFinset_subset f hf_fin subset_union_right)
      _ ≤ ∏ w ∈ S, f w := prod_le_prod_of_subset_of_le_one₀ subset_union_left
        (fun w _ ↦ norm_nonneg _) fun w _ hw ↦ by simpa [f] using (mem_integralOff S).1 hy_int w hw
  rw [Real.sqrt_le_left (by positivity)]
  calc genIndex (ratToPlaces S y)
    _ = (∏ w ∈ S, f w)⁻¹ := h_index
    _ ≤ |(Algebra.norm ℚ y : ℝ)| := inv_le_of_inv_le₀ (by simp [hy_ne]) h_inv_le
    _ = (∏ v : InfinitePlace E, ‖Φ v y‖) ^ 2 := by rw [abs_norm_eq_prod_norm_sq, prod_pow]

/-! ### The involution -/

/-- The finite set `S` of finite places of `E` is stable under complex conjugation. -/
abbrev _root_.Finset.StarStable [IsCMField E] : Prop := Fact (∀ w ∈ S, star w ∈ S)

variable {S} in
lemma star_mem_of_starStable [IsCMField E] [hS : S.StarStable] {w : FinPlace E} (hw : w ∈ S) :
    star w ∈ S :=
  hS.out w hw

variable [IsCMField E] [S.StarStable]

/-- The involution of `LocProd S`: the component of `star x` at `w` is the conjugate of the
component of `x` at `star w`. -/
instance : StarRing (LocProd S) :=
  starRingOfInvolution
    (.pi fun w ↦ (conjLoc (star_star w.val)).comp
      (evalRingHom _ (⟨star w.val, star_mem_of_starStable w.prop⟩ : S)))
    fun x ↦ by
      obtain ⟨y, rfl⟩ : ∃ y : 𝔸f E, evalPlaces S y = x := ⟨_, evalPlaces_adeleOfLocal S x⟩
      simp [funext_iff, ← finAdele_star_apply]

@[simp]
lemma star_evalPlaces (x : 𝔸f E) : star (evalPlaces S x) = evalPlaces S (star x) := rfl

/-- For `S` stable under complex conjugation, extension by zero commutes with conjugation. -/
lemma adeleOfLocal_star (x : LocProd S) : adeleOfLocal S (star x) = star (adeleOfLocal S x) := by
  -- Write `x = evalPlaces S y`. The map `adeleOfLocal S ∘ evalPlaces S` multiplies by `idem S`,
  -- which `star` fixes because `S` is stable under `star`.
  have hS : star ⁻¹' (S : Set (FinPlace E)) = S :=
    Set.ext fun w ↦ ⟨fun hw ↦ by simpa using star_mem_of_starStable hw, star_mem_of_starStable⟩
  obtain ⟨y, rfl⟩ : ∃ y : 𝔸f E, evalPlaces S y = x := ⟨_, evalPlaces_adeleOfLocal S x⟩
  rw [star_evalPlaces, adeleOfLocal_evalPlaces, adeleOfLocal_evalPlaces, star_mul', star_idem, hS]

instance : ContinuousStar (LocProd S) where
  continuous_star := continuous_pi fun w ↦ (continuous_locMap (starRingEnd E)
    (star_eq_iff_star_eq.mp (star_star w.val))).comp (continuous_apply _)

-- `O` is the image of `Ô E` under `evalPlaces S`, which commutes with `star`; the witnesses for
-- `Ô E` project to witnesses for `O`.
instance [HasPrimitiveRoot5040 E] : IsAdelic (O : Subring (LocProd S)) where
  isOpen_isCompact := ⟨isOpen_O, isCompact_O⟩
  isValuationPair := SemilocalField.isValuationPair
  star_mem := by
    rw [locProd_O_eq_map_evalPlaces]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨star a, IsStarStable.star_mem ha, (star_evalPlaces S a).symm⟩
  exists_skew_unit := by
    obtain ⟨i, hi, τ, hτ, hi_sq, hi_star, hτ_trace⟩ := (isAdelic_Ô (E := E)).exists_skew_unit
    exact ⟨evalPlaces S i, ((mem_Ô_iff S).1 hi).left, evalPlaces S τ, ((mem_Ô_iff S).1 hτ).left,
      by rw [← map_neg, ← map_mul, hi_sq, map_one], by rw [star_evalPlaces, hi_star, map_neg],
      by rw [star_evalPlaces, ← map_add, hτ_trace, map_one]⟩
  exists_norm_neg_one := by
    obtain ⟨c, hc, hc_norm⟩ := (isAdelic_Ô (E := E)).exists_norm_neg_one
    exact ⟨evalPlaces S c, ((mem_Ô_iff S).1 hc).left,
      by rw [star_evalPlaces, ← map_mul, hc_norm, map_neg, map_one]⟩

end SemilocalPlace

end New

end
