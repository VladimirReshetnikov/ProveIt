import Lib.ClassField.Places.Ideles
import Lib.Weil.DualPair.Kronecker

/-!
# The module of an idele, Haar measure scaling and the norm map on finite adeles

This file studies the module of an idele of a number field `E`, its relation to Haar measure, and
its behaviour under norms. Here `New.𝔸 E` has one copy of `ℂ` for each infinite place. The module
`New.ideleAbs` is therefore the product of the squared norms at the infinite places and of the norms
at the finite places. The generalised index `New.genIndex a` of a finite idele, defined through the
scaling of Haar measure, is the inverse of its module; it is `[Ô : a Ô]` when `a` is integral. For
an extension `L / K` of number fields, the algebra norm `New.adeleNorm` on finite adeles preserves
the module.

## Main definitions and results

* `New.ideleAbs`: the module is multiplicative, and it is a continuous positive character
  (`New.continuous_ideleAbs`, `New.ideleAbs_pos`).
* `New.ideleAbs_toAdele`: the product formula for the diagonal embedding `New.toAdele`, for a
  totally complex `E`.
* `New.finIdeleAbs`: the module `∏ ‖x_w‖` of a finite idele; `New.finIdeleAbs_principalIdele` is the
  finite part of the product formula.
* `New.genIndex_eq_inv_finIdeleAbs`, `New.genIndex_eq_inv_norm`: for a finite idele, or an element
  of `E_wˣ`, the index `New.genIndex` is the inverse of its module.
* `New.map_mulVec_haar_finAdele`, `New.volume_map_mulVec_adele`, `New.volume_map_mul_mul_adele`:
  pushing Haar measure forward along `x ↦ a x` or `x ↦ a x b` divides it by the module of the
  determinant of that map.
* `New.finIdeleAbs_adeleNorm`: the norm keeps the module `New.finIdeleAbs` of a finite idele.

Notions from other files:
* `New.𝔸f E`, `New.Ô E`: the finite adeles of `E`, and the subring of those that are integral at
  every finite place.
* `New.FinPlace E`, `New.LocField w`: the finite places of `E` and the completion `E_w`; `w.q` is
  the order of the residue field at `w`, and `w.below K` is the place of a subfield `K` below `w`.
* `New.locIdele w x`: the finite idele with component `x` at `w` and `1` elsewhere.
* `New.idelesUnitOff S`: the finite ideles that are units at all places outside `S`.
* `New.genIndex a`: the inverse of the factor by which multiplication by a unit `a` scales Haar
  measure, and `0` for a non-unit.

## Relation to the literature

Known result: the module of an idele, the product formula and the scaling of Haar measure.

Part of a known result: functoriality of ideles under the norm map, restricted here to the module
and to supports.
-/

/-!
## The module of an idele and the product formula

* `New.ideleAbs_star`, `New.ideleAbs_eq_one_of_mem_unitary`: for a CM field, the module is invariant
  under conjugation, and unitary ideles have module `1`.
-/

section AdelicAbs

open NumberField FinitePlace MonoidHom Valued

namespace New

variable {E : Type*} [Field E] [NumberField E] {x : (𝔸 E)ˣ}

/-- The module `|x|` of an element of `(𝔸 E)ˣ`, as a homomorphism to `ℝ`: the product of the
squared norms of the components at the infinite places (each a copy of `ℂ`) and of the norms at the
finite places. For a totally complex `E` this is the idelic module. -/
noncomputable def ideleAbs : (𝔸 E)ˣ →* ℝ where
  toFun x := (∏ w : InfinitePlace E, ‖(x : 𝔸 E).1 w‖ ^ 2) *
    ∏ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(x : 𝔸 E).2 w‖
  map_one' := by simp
  map_mul' x y := by
    -- an idele is a unit at almost all finite places, so the infinite product splits
    have h_finite (z : (𝔸 E)ˣ) : (Function.mulSupport fun w ↦ ‖(z : 𝔸 E).2 w‖).Finite := by
      refine (finite_setOf_valued_val_ne_one (z.map (snd _ (𝔸f E)))).subset ?_
      simp +contextual [norm_def, not_imp_not]
    simp [sq, field, finprod_mul_distrib (h_finite x) (h_finite y), Finset.prod_mul_distrib]

lemma ideleAbs_apply (x : (𝔸 E)ˣ) :
    ideleAbs x =
      (∏ w : InfinitePlace E, ‖(x : 𝔸 E).1 w‖ ^ 2) * ∏ᶠ w : FinPlace E, ‖(x : 𝔸 E).2 w‖ := rfl

@[simp]
lemma ideleAbs_nonneg_and_ne_zero : 0 ≤ ideleAbs x ∧ ideleAbs x ≠ 0 := by
  refine ⟨mul_nonneg ?_ (finprod_nonneg fun w ↦ norm_nonneg _), (toHomUnits ideleAbs x).ne_zero⟩
  positivity

@[simp]
lemma ideleAbs_pos : 0 < ideleAbs x :=
  lt_of_le_of_ne' ideleAbs_nonneg_and_ne_zero.1 ideleAbs_nonneg_and_ne_zero.2

/-- If the idele `x` has valuation `1` at every finite place, then its module is the product of the
squared norms of its components at the infinite places. -/
lemma ideleAbs_eq_prod_of_v_eq_one (hx_unit : ∀ w : FinPlace E, v ((x : 𝔸 E).2 w) = 1) :
    ideleAbs x = ∏ w : InfinitePlace E, ‖(x : 𝔸 E).1 w‖ ^ 2 := by
  simp [ideleAbs_apply, norm_def, hx_unit]

/-- A finite idele that is a unit at every finite place has module `1`. -/
lemma ideleAbs_finIdeleIncl_eq_one {y : (𝔸f E)ˣ} (hy : y ∈ idelesUnitOff ∅) :
    ideleAbs (finIdeleIncl y) = 1 := by
  simp [ideleAbs_eq_prod_of_v_eq_one (x := finIdeleIncl y) (by simpa using hy)]

/-- The module `ideleAbs` is continuous on the idele group of `E`. -/
@[fun_prop]
lemma continuous_ideleAbs : Continuous (ideleAbs (E := E)) := by
  -- near `1` the finite components are units, so only the infinite places contribute
  refine continuous_of_continuousAt_one _ ?_
  have h_near : ∀ᶠ x : (𝔸 E)ˣ in nhds 1, x.map (snd _ (𝔸f E)) ∈ idelesUnitOff ∅ :=
    ((isOpen_idelesUnitOff ∅).preimage (continuous_snd.units_map _)).mem_nhds (by simp)
  refine ContinuousAt.congr
    (f := fun x : (𝔸 E)ˣ ↦ ∏ w : InfinitePlace E, ‖(x : 𝔸 E).1 w‖ ^ 2) (by fun_prop) ?_
  filter_upwards [h_near] with x hx using (ideleAbs_eq_prod_of_v_eq_one (by simpa using hx)).symm

/-- For `x : E`, the product of the norms of the components of the principal finite adele `x` is the
product of `w x` over Mathlib's finite places `w` of `E`. -/
lemma finprod_norm_algebraMap_apply (x : E) :
    ∏ᶠ w : FinPlace E, ‖algebraMap E (𝔸f E) x w‖ = ∏ᶠ w : FinitePlace E, w x := by
  rw [← finprod_comp_equiv equivHeightOneSpectrum.symm]
  exact finprod_congr fun w ↦ (equivHeightOneSpectrum_symm_apply w x).symm

/-- The product formula: for a totally complex `E`, the principal idele of an element of `Eˣ` (its
image under the diagonal embedding `toAdele`) has module `1`. The class `PlaceEmbedding E` chooses
a complex embedding for each infinite place. -/
lemma ideleAbs_toAdele [IsTotallyComplex E] [PlaceEmbedding E] (x : Eˣ) :
    ideleAbs (E := E) (x.map (toAdele (E := E))) = 1 :=
  calc
    _ = (∏ w : InfinitePlace E, w x ^ w.mult) * ∏ᶠ w : FinPlace E, ‖algebraMap E (𝔸f E) x w‖ := by
      simp [ideleAbs_apply, ← InfinitePlace.apply]
    _ = 1 := by rw [finprod_norm_algebraMap_apply, prod_abs_eq_one x.ne_zero]

variable [IsCMField E]

/-- For a CM field `E`, the module of an idele `x` is invariant under complex conjugation. -/
@[simp]
lemma ideleAbs_star : ideleAbs (star x) = ideleAbs x := by
  -- conjugation keeps the infinite absolute values and permutes the finite places
  have h_inf : ∏ w : InfinitePlace E, ‖(↑(star x) : 𝔸 E).1 w‖ ^ 2 =
      ∏ w : InfinitePlace E, ‖(x : 𝔸 E).1 w‖ ^ 2 := by simp
  have h_fin : ∏ᶠ w : FinPlace E, ‖(↑(star x) : 𝔸 E).2 w‖ = ∏ᶠ w : FinPlace E, ‖(x : 𝔸 E).2 w‖ :=
    finprod_eq_of_bijective star star_involutive.bijective fun w ↦
      show ‖(↑(star x) : 𝔸 E).2 w‖ = ‖(x : 𝔸 E).2 (star w)‖ by simp [norm_def]
  rw [ideleAbs_apply, ideleAbs_apply, h_inf, h_fin]

/-- For a CM field `E`, a unitary idele `x` (one with `star x * x = 1`) has module `1`. -/
lemma ideleAbs_eq_one_of_mem_unitary (hx : (x : 𝔸 E) ∈ unitary (𝔸 E)) : ideleAbs x = 1 := by
  have h_norm : star x * x = 1 := Units.ext (Unitary.star_mul_self_of_mem hx)
  have h_sq : ideleAbs x ^ 2 = 1 := by simpa [sq] using congrArg ideleAbs h_norm
  exact (pow_eq_one_iff_of_nonneg ideleAbs_pos.le two_ne_zero).1 h_sq

end New

end AdelicAbs

/-!
## Scaling of Haar measure by the module

The index `New.genIndex` is first compared with the module. Both are multiplicative, so at a single
place `w` it is enough, by `New.eq_norm_inv_of_uniformizer`, to treat uniformisers, whose index is
the order `w.q` of the residue field.

Conventions: `v` is the multiplicative valuation, `exp (-1)` on uniformisers.
-/

section AdelicModulus

open NumberField Fintype MeasureTheory RingHom Matrix Prod Measure WithZero Valued LinearMap Units
  Valuation IsUniformizer IsRankOneDiscrete Subgroup FinitePlace Algebra

namespace New

variable {E n : Type*} [Field E] [NumberField E] [Fintype n] [DecidableEq n] {w : FinPlace E}

/-! ### Valuations and absolute values at a finite place -/

/-- An element `y` of `E_w` has valuation less than `1` if and only if its quotient by the chosen
uniformiser is integral. -/
lemma v_uniformizer_inv_mul_le_one_iff {y : IsDedekindDomain.HeightOneSpectrum.adicCompletion E w} :
    v ((uniformizer w).val⁻¹ * y) ≤ 1 ↔ v y < 1 := by
  simp [← lt_mul_exp_iff_le]

/-- The norm of a nonzero `x` in `E_w` is `w.q ^ k`, where `w.q` is the order of the residue field
and `v x = exp k`. -/
lemma norm_locField_eq_q_zpow {x : LocField w} (hx : x ≠ 0) : ‖x‖ = w.q ^ (v x).log := by
  simp [FinitePlace.norm_def, WithZeroMulInt.toNNReal, hx]

/-- A homomorphism `χ : E_wˣ → ℝ` that takes the value `w.q`, the order of the residue field, on
every uniformiser is the inverse of the normalised absolute value. -/
lemma eq_norm_inv_of_uniformizer (χ : (LocField w)ˣ →* ℝ)
    (hχ : ∀ {x : (LocField w)ˣ}, v x.val = exp (-1) → χ x = w.q) {x : (LocField w)ˣ} :
    χ x = ‖x.val‖⁻¹ := by
  -- With `π = uniformizer w` and `k = (v x).log`, both `π` and `x * π ^ k * π` are uniformisers, so
  -- `χ` is `w.q` on both. Hence `χ x * w.q ^ k = 1`, and `‖x‖ = w.q ^ k`.
  have h_prod : χ (x * uniformizer w ^ (v x.val).log * uniformizer w) = w.q :=
    hχ (by simp [WithZero.exp_neg, -inv_exp])
  have h_mul : χ x * (w.q : ℝ) ^ (v x.val).log = 1 := by simpa [hχ (v_uniformizer w)] using h_prod
  rw [norm_locField_eq_q_zpow x.ne_zero, eq_inv_of_mul_eq_one_left h_mul]

/-- For finite adeles `a`, `b` there is an idempotent `e` of `Ô`, the ring of integral finite
adeles, such that both lie in the `Ô`-module generated by the patch `a - e * (a - b)`
(`New.IsValuationPair`). -/
lemma isValuationPair_Ô : IsValuationPair (Ô E) := by
  -- The idempotent `idem S` is `1` at the places in `S` and `0` elsewhere.
  -- Patch along the places where `v (a w) ≤ v (b w)`: the patch is `b w` there and `a w` elsewhere,
  -- so at each place it has the larger of the two valuations.
  intro a b
  let S : Set (FinPlace E) := {w | v (a w) ≤ v (b w)}
  have h_idem : idem S * idem S = idem S := DFunLike.ext _ _ fun w ↦ by simp [idem_apply]
  have h_le (w : FinPlace E) :
      v (a w) ≤ v ((a - idem S * (a - b)) w) ∧ v (b w) ≤ v ((a - idem S * (a - b)) w) := by
    by_cases hw : v (a w) ≤ v (b w) <;> simp [S, hw, le_of_not_ge]
  refine ⟨⟨idem S, idem_mem_Ô S⟩, h_idem, ?_⟩
  change Ô E ∙ a ⊔ Ô E ∙ b ≤ Ô E ∙ (a - idem S * (a - b))
  simpa [exists_eq_mul_iff_v_le] using forall_and.1 h_le

instance [IsCMField E] : IsStarStable (Ô E) := ⟨star_mem_Ô⟩

/-! ### The module of a finite idele -/

/-- The module `|x|` of a finite idele `x`: the module `New.ideleAbs` of the idele with finite part
`x` and component `1` at the infinite places. -/
noncomputable def finIdeleAbs : (𝔸f E)ˣ →* ℝ := ideleAbs.comp finIdeleIncl

lemma finIdeleAbs_apply (x : (𝔸f E)ˣ) : finIdeleAbs x = ∏ᶠ w : FinPlace E, ‖x.val w‖ := by
  simp [finIdeleAbs, ideleAbs_apply]

/-- The product formula, finite part: for `x` in `Eˣ`, with `principalIdele x` its diagonal image in
`(𝔸f E)ˣ`, the product of the normalised absolute values `|x|_w` over the finite places is
`|N_{E/ℚ}(x)|⁻¹`. -/
@[simp]
lemma finIdeleAbs_principalIdele (x : Eˣ) :
    finIdeleAbs (principalIdele (x : Eˣ)) = |Algebra.norm ℚ x.val|⁻¹ := by
  rw [← prod_eq_inv_abs_norm x.ne_zero, ← finprod_norm_algebraMap_apply, finIdeleAbs_apply]
  rfl

@[simp]
lemma finIdeleAbs_locIdele (x : (LocField w)ˣ) : finIdeleAbs (locIdele w x) = ‖x.val‖ := by
  simp +contextual [finIdeleAbs_apply, finprod_eq_single _ w]

/-! ### The generalised index as the inverse of the module -/

/-- Reduction modulo `w` maps the integral finite adeles onto the residue field at `w`. -/
lemma reduceAt_surjective (w : FinPlace E) : Function.Surjective (reduceAt w) := fun y ↦ by
  obtain ⟨a, rfl⟩ := algebraMap_ResField_surjective w y
  exact ⟨algebraMap (𝓞 E) (Ô E) a, reduceAt_algebraMap w a⟩

/-- For a uniformiser `x` at `w`, let `a` be the finite idele with component `x` at `w` and `1`
elsewhere. Its generalised index `[Ô : a Ô]` is the order `w.q` of the residue field. -/
lemma genIndex_locIdele_of_v_eq_exp_neg_one {x : (LocField w)ˣ} (hx : v x.val = exp (-1)) :
    genIndex (locIdele w x).val = w.q := by
  -- The idele generates the kernel of reduction modulo `w`, which maps `Ô` onto the residue field.
  have h_mem : (locIdele w x).val ∈ Ô E := by
    simp +contextual +decide [mem_Ô, ← and_forall_ne w, hx]
  have h_ker : Ideal.span {(⟨(locIdele w x).val, h_mem⟩ : Ô E)} = RingHom.ker (reduceAt w) := by
    ext y
    -- divisibility is tested place by place, and away from `w` the condition is integrality of `y`
    have h_dvd : (∃ z ∈ Ô E, y.val = (locIdele w x).val * z) ↔ v (y.val w) < 1 := by
      simp +contextual [exists_eq_mul_iff_v_le, ← and_forall_ne w, mem_Ô.1, hx, ← lt_mul_exp_iff_le,
        ← WithZero.exp_add]
    simpa [Ideal.mem_span_singleton, Subtype.ext_iff, dvd_def] using h_dvd
  rw [genIndex_eq_card isOpen_Ô isCompact_Ô h_mem (Units.isUnit _), h_ker,
    Nat.card_congr (quotientKerEquivOfSurjective (reduceAt_surjective w)).toEquiv, card_ResField]

/-- The generalised index `genIndex` of a finite idele, the inverse of the factor by which it scales
Haar measure, is the inverse of its module. -/
lemma genIndex_eq_inv_finIdeleAbs (a : (𝔸f E)ˣ) : genIndex a.val = (finIdeleAbs a)⁻¹ := by
  -- The two sides agree on a subgroup `H`. It contains the unit ideles, so it is open and closed,
  -- and it suffices to treat ideles with one component (`mem_of_locIdele_mem`), and then local
  -- uniformisers.
  let χ : (𝔸f E)ˣ →* ℝ := genIndex.toMonoidHom.comp (coeHom (𝔸f E))
  let H : Subgroup (𝔸f E)ˣ := χ.eqLocus (invMonoidHom.comp finIdeleAbs)
  have mem_H {b : (𝔸f E)ˣ} : b ∈ H ↔ genIndex b.val = (finIdeleAbs b)⁻¹ := Iff.rfl
  -- a unit of `Ô` has index `1` and module `1`
  have h_units : idelesUnitOff ∅ ≤ H := fun u hu ↦ by
    have hu_val : ∀ w : FinPlace E, v (u.val w) = 1 := by simpa using hu
    have h_index : genIndex u.val = 1 := by
      simp [genIndex_eq_card isOpen_Ô isCompact_Ô, mem_Ô, hu_val, Nat.card_unique]
    simp [mem_H, h_index, finIdeleAbs, ideleAbs_finIdeleIncl_eq_one hu]
  have h_loc (w : FinPlace E) (x : (LocField w)ˣ) : locIdele w x ∈ H := by
    have h_char : (χ.comp (locIdele w)) x = ‖x.val‖⁻¹ :=
      eq_norm_inv_of_uniformizer (χ.comp (locIdele w)) genIndex_locIdele_of_v_eq_exp_neg_one
    simpa [mem_H, χ] using h_char
  have h_closed : IsClosed (H : Set (𝔸f E)ˣ) :=
    isClosed_of_isOpen H (isOpen_mono h_units (isOpen_idelesUnitOff ∅))
  exact mem_H.1 (mem_of_locIdele_mem h_closed fun w ↦ h_loc w _)

/-- The generalised index `genIndex` of an element of `E_wˣ`, the inverse of the factor by which it
scales Haar measure on `E_w`, is the inverse of its absolute value. -/
lemma genIndex_eq_inv_norm (a : (LocField w)ˣ) : genIndex a.val = ‖a.val‖⁻¹ := by
  -- A uniformiser `x` generates the maximal ideal of the local integers, so its index is the order
  -- of the residue field.
  refine eq_norm_inv_of_uniformizer (genIndex.toMonoidHom.comp (coeHom _)) fun {x} hx ↦ ?_
  change genIndex x.val = w.q
  have hx_int : x.val ∈ LocInt w := show v x.val ≤ 1 by simp +decide [hx]
  have h_max : IsLocalRing.maximalIdeal (LocInt w) = Ideal.span {⟨x.val, hx_int⟩} :=
    is_generator (π := ⟨x.val, hx_int⟩) <| show v.IsUniformizer x.val by
      simp [IsUniformizer.iff, generator_eq_exp_neg_one_of_mem_range ⟨x.val, hx⟩, hx]
  calc genIndex x.val = Nat.card (LocInt w ⧸ Ideal.span {(⟨x.val, hx_int⟩ : LocInt w)}) :=
      genIndex_eq_card (Valued.isOpen_valuationSubring _) (isCompact_LocInt w) hx_int x.isUnit
    _ = Nat.card (LocInt w ⧸ IsLocalRing.maximalIdeal (LocInt w)) := by rw [h_max]
    _ = w.q := Nat.cast_inj.2 (card_ResField w)

/-! ### Linear maps and Haar measure -/

/-- For a finite index type `n` and `a` in `GL_n` of the finite adeles, `x ↦ a x` pushes a Haar
measure `μ` on vectors forward to `μ` divided by the module `New.finIdeleAbs` of the finite idele
`det a`. -/
lemma map_mulVec_haar_finAdele (μ : Measure (n → 𝔸f E)) [IsAddHaarMeasure μ] (a : GL n (𝔸f E)) :
    μ.map (fun x : n → 𝔸f E ↦ a.val *ᵥ x) = ENNReal.ofReal (finIdeleAbs a.det)⁻¹ • μ := by
  -- `a` scales Haar measure on vectors as `det a` does on the finite adeles.
  calc μ.map (fun x : n → 𝔸f E ↦ a • x)
    _ = ENNReal.ofReal (distribHaarChar (n → 𝔸f E) a : ℝ)⁻¹ • μ :=
      map_smul_eq_inv_distribHaarChar_smul a
    _ = ENNReal.ofReal (genIndex a.det.val) • μ := by
      rw [inv_distribHaarChar_GL_eq_genIndex_det isOpen_Ô isCompact_Ô isValuationPair_Ô,
        GeneralLinearGroup.val_det_apply]
    _ = ENNReal.ofReal (finIdeleAbs a.det)⁻¹ • μ := by rw [genIndex_eq_inv_finIdeleAbs]

/-- For `a` in `GL_n` of the adeles `𝔸 E`, with `n` a finite index type, the map `x ↦ a x` pushes
the Haar measure `volume` on adelic `n`-vectors forward to itself divided by the module
`New.ideleAbs` (the adelic absolute value) of `det a`. -/
lemma volume_map_mulVec_adele (a : GL n (𝔸 E)) :
    volume.map (fun x : n → 𝔸 E ↦ a.val *ᵥ x) = ENNReal.ofReal (ideleAbs a.det)⁻¹ • volume := by
  -- Split vectors into their infinite and finite parts; `a` scales each factor of the measure.
  let aInf : GL n (InfinitePlace E → ℂ) := a.map (RingHom.fst _ (𝔸f E))
  let aFin : GL n (𝔸f E) := a.map (RingHom.snd (InfinitePlace E → ℂ) _)
  let rInf : ℝ := ∏ w : InfinitePlace E, ‖a.val.det.1 w‖ ^ 2
  let rFin : ℝ := ∏ᶠ w : FinPlace E, ‖a.val.det.2 w‖
  let L : (n → InfinitePlace E → ℂ) ≃ₗ[ℝ] _ := aInf.toLin.toLinearEquiv.restrictScalars ℝ
  have h_norm (z : InfinitePlace E → ℂ) : Algebra.norm ℝ z = ∏ w, ‖z w‖ ^ 2 := by
    -- multiplication by `z` acts on each copy of `ℂ` separately
    change LinearMap.det (LinearMap.pi fun w ↦ LinearMap.mul ℝ ℂ (z w) ∘ₗ LinearMap.proj w) = _
    rw [det_pi]
    exact Finset.prod_congr rfl fun w _ ↦
      (Algebra.norm_complex_apply (z w)).trans (Complex.sq_norm (z w)).symm
  have h_det : LinearMap.det L.toLinearMap = rInf := by
    change LinearMap.det ((toLin' (a.val.map (RingHom.fst _ (𝔸f E)))).restrictScalars ℝ) = rInf
    rw [det_restrictScalars, det_toLin', h_norm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have h_inf : Measure.map L.toLinearMap addHaar = ENNReal.ofReal rInf⁻¹ • addHaar := by
    simpa [h_det, rInf, Finset.prod_pow] using
      map_linearMap_addHaar_eq_smul_addHaar addHaar L.isUnit_det'.ne_zero
  have h_fin : volume.map (aFin.val *ᵥ ·) = ENNReal.ofReal rFin⁻¹ • volume := by
    simpa [rFin, aFin, finIdeleAbs, ideleAbs, GeneralLinearGroup.map_det] using
      map_mulVec_haar_finAdele volume aFin
  have h_prod : MeasurePreserving (Prod.map L.toLinearMap (aFin.val *ᵥ ·)) (addHaar.prod volume)
      ((ENNReal.ofReal rInf⁻¹ • addHaar).prod (ENNReal.ofReal rFin⁻¹ • volume)) :=
    .prod ⟨L.toLinearMap.continuous_of_finiteDimensional.measurable, h_inf⟩ ⟨by fun_prop, h_fin⟩
  -- Transport this scaling along the splitting of vectors.
  let split : (n → 𝔸 E) ≃ₜ+ (n → InfinitePlace E → ℂ) × (n → 𝔸f E) :=
    { toEquiv := Equiv.arrowProdEquivProdArrow _ _ _, map_add' := fun _ _ ↦ rfl }
  refine map_addHaar_eq_smul_of_semiconj _ split (fun x ↦ ?_) h_prod.measurable
    (h_prod.map_eq.trans ?_)
  · -- taking components commutes with the sums that define `a *ᵥ x`
    exact Prod.ext (funext fun _ ↦ fst_sum) (funext fun _ ↦ snd_sum)
  · -- the module of `det a` is the product of the two factors
    simp [rInf, rFin, ideleAbs, prod_smul_left, prod_smul_right, mul_smul, finprod_nonneg]

/-- The determinant of the conjugate transpose of a matrix in GL_n of the adeles is the conjugate of
its determinant. -/
@[simp]
lemma det_star [IsCMField E] (a : GL n (𝔸 E)) : (star a).det = star a.det :=
  ext (det_conjTranspose _)

/-- For a finite index type n, a in GL_n(𝔸) and b in GL_1(𝔸), the map x ↦ axb on n×1 adelic matrices
pushes the standard measure forward to |det(b)^n det a|⁻¹ times itself, with |·| the module of an
idele. -/
lemma volume_map_mul_mul_adele (a : GL n (𝔸 E)) (b : GL Unit (𝔸 E)) :
    volume.map (fun x : Matrix n Unit (𝔸 E) ↦ a.val * x * b.val) =
      ENNReal.ofReal (ideleAbs (b.det ^ card n * a.det))⁻¹ • volume := by
  -- Vectorising turns `x ↦ a * x * b` into multiplication by the Kronecker product `bᵀ ⊗ a`,
  -- whose determinant is `b.det ^ card n * a.det`.
  let vecEquiv : Matrix n Unit (𝔸 E) ≃ₜ+ (Unit × n → 𝔸 E) :=
    { toFun := vec, invFun y i j := y (j, i), map_add' := vec_add }
  let c : GL (Unit × n) (𝔸 E) := kroneckerGL (transposeGL b) a
  have det_eq : c.det = b.det ^ card n * a.det :=
    Units.ext (by simp [c, kroneckerGL, det_kronecker])
  have h_semiconj (x : Matrix n Unit (𝔸 E)) : vecEquiv (a.val * x * b.val) = c.val *ᵥ vecEquiv x :=
    (kronecker_mulVec_vec a.val x b.valᵀ).symm
  rw [← det_eq]
  exact map_addHaar_eq_smul_of_semiconj _ vecEquiv h_semiconj (by fun_prop)
    (volume_map_mulVec_adele c)

end New

end AdelicModulus

/-!
## The generalised index of a field element

* `New.genIndex_natCast`: for a natural number `k` and a CM field `E` it is `(k ^ r) ^ 2`, with
  `r` the number of infinite places of `E`.
-/

section IndexOfRationals

variable {E : Type*} [Field E] [NumberField E]

/-- For a number field `E`, the generalised index `New.genIndex` of `x : E`, as a finite adele, is
the absolute value of the norm of `x` to `ℚ`. -/
@[simp]
lemma New.genIndex_algebraMap (x : E) : genIndex (x : 𝔸f E) = |↑(Algebra.norm ℚ x)| := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [genIndex.map_nonunit]
  · -- `genIndex` is the inverse of `finIdeleAbs` on ideles, which the product formula computes
    simpa using genIndex_eq_inv_finIdeleAbs (principalIdele (Units.mk0 x hx))

/-- For a natural number `k` the generalised index `New.genIndex` of `k` as a finite adele is
`(k ^ r) ^ 2`, with `r = Core.numInfPlaces E` the number of infinite places of the CM field `E`. The
reason is that the norm of `k` is `k ^ [E : ℚ]` and `[E : ℚ] = 2r`. -/
lemma New.genIndex_natCast [NumberField.IsCMField E]
    (k : ℕ) : genIndex (k : 𝔸f E) = (k ^ Core.numInfPlaces E) ^ 2 := by
  simpa [Algebra.norm_natCast, finrank_eq_two_mul_card_infinitePlace, pow_mul'] using
    genIndex_algebraMap (k : E)

end IndexOfRationals

/-!
## The norm map on finite adeles

For an extension `L / K` of number fields the finite adeles of `L` are a finite free module over
those of `K` (`New.adeleBasis`), so they have an algebra norm `New.adeleNorm`. It is continuous and
extends the field norm, so identities can be checked on the dense field.
-/

section AdeleNorm

open Module Algebra NumberField Units

namespace New

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

instance : Free (𝔸f K) (𝔸f L) := .of_basis (adeleBasis (finBasis K L))

instance : Module.Finite (𝔸f K) (𝔸f L) := .of_basis (adeleBasis (finBasis K L))

/-- For an extension L/K of number fields, the algebra norm from the finite adeles of L to the
finite adeles of K, as a multiplicative map. -/
noncomputable abbrev adeleNorm : 𝔸f L →* 𝔸f K := Algebra.norm (S := 𝔸f L) (𝔸f K)

/-- The norm map from the finite adeles of `L` to those of `K` is continuous. -/
@[fun_prop]
lemma continuous_adeleNorm : Continuous (adeleNorm K L) := by
  -- Pull back along the coordinates for a basis of `L / K`, a homeomorphism; there the norm is the
  -- determinant of a matrix that depends linearly on the coordinates.
  rw [(isHomeomorph_adeleCombination (finBasis K L)).isQuotientMap.continuous_iff]
  simp only [Fintype.linearCombination, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_def,
    norm_eq_matrix_det (Free.chooseBasis ..), map_sum, map_smul]
  fun_prop

/-- The norm of an element `x` of `L`, regarded as a finite adele, is the field norm of `x`. -/
@[simp]
lemma adeleNorm_algebraMap (x : L) : adeleNorm K L x = Algebra.norm K x := by
  -- A basis of `L / K` is also a basis of the adeles (`adeleBasis`), and multiplication by `x` has
  -- the same matrix in both, as elements of `L` have the same coordinates in both.
  let b : Basis (Fin (finrank K L)) K L := finBasis K L
  have h_repr (z : L) (i : Fin (finrank K L)) :
      (adeleBasis b).repr (z : 𝔸f L) i = (b.repr z i : 𝔸f K) := by
    simp [adeleBasis, ← adeleCombination_repr b]
  have h_mat : leftMulMatrix (adeleBasis b) (x : 𝔸f L) =
      (leftMulMatrix b x).map (algebraMap K (𝔸f K)) := by
    ext i j : 1
    simp [leftMulMatrix_eq_repr_mul, ← h_repr, adeleBasis]
  rw [norm_eq_matrix_det (adeleBasis b), h_mat, norm_eq_matrix_det b, RingHom.map_det]
  rfl

/-- For `a` a finite adele of `K`, the norm to `K` of its image in the adeles of `L` is
`a ^ [L : K]`. -/
lemma adeleNorm_finAdeleIncl (a : 𝔸f K) :
    adeleNorm K L (finAdeleIncl K L a) = a ^ finrank K L := by
  -- both sides are continuous, so it suffices to compare them on the dense subset `K`
  revert a
  exact denseRange_algebraMap_finAdele.eq (by simp) (by fun_prop) (by fun_prop)

/-- For Galois `L / K`, the norm of a finite adele `y` of `L`, included back in the adeles of `L`,
is the product of the images of `y` under the Galois group. -/
lemma finAdeleIncl_adeleNorm [IsGalois K L] :
    ∀ y : 𝔸f L, finAdeleIncl K L (adeleNorm K L y) = ∏ σ : Gal(L/K), adeleMap σ y :=
  -- both sides are continuous, so it suffices to compare them on the dense subset `L`
  denseRange_algebraMap_finAdele.eq (by simp [norm_eq_prod_automorphisms])

variable {L} in
/-- For an extension L/K, a finite place w of L and v = `FinPlace.below K w` the place of K below w,
the local norm L_w^× → K_v^×: the v-component of the adelic norm of the idele supported at w. -/
noncomputable def localNorm (w : FinPlace L) : (LocField w)ˣ →* (LocField (FinPlace.below K w))ˣ :=
  ((ideleAt (w.below K)).comp (map (adeleNorm K L))).comp (locIdele w)

variable {K L}

lemma adeleNorm_mem_Ô {y : 𝔸f L} (hy : y ∈ Ô L) : adeleNorm K L y ∈ Ô K := by
  -- `𝓞 L` is dense in `Ô L`, the set `Ô K` is closed, and norms of integers are integers
  refine Set.MapsTo.closure_left ?_ (by fun_prop) isCompact_Ô.isClosed
    (Subtype.dense_iff.1 denseRange_algebraMap_Ô hy)
  simpa using fun a ↦ isIntegral_norm K a.prop

/-- For number fields L/K, a finite place w of L and y in L_w^×, the norm to K of the finite idele
`locIdele w y` (y at w and 1 elsewhere) has component `localNorm K w y` at the place below w and 1
at every other place. -/
lemma adeleNorm_locIdele (w : FinPlace L) (y : (LocField w)ˣ) :
    (locIdele w y).map (adeleNorm K L) = locIdele (FinPlace.below K w) (localNorm K w y) := by
  ext v : 2
  by_cases hv : v = w.below K
  · subst hv
    simp [localNorm, ideleAt]
  · -- Let `e` be the image in `𝔸f L` of the idempotent at `v`. It vanishes at `w`, and
    -- `locIdele w y` is `1` away from `w`, so `e * locIdele w y = e`.
    let e : 𝔸f L := finAdeleIncl K L (idem {v})
    have e_mul : e * (locIdele w y).1 = e := by
      simp_all [e, DFunLike.ext_iff, ← and_forall_ne w, adeleMap_apply, eq_comm]
    -- Take norms and look at `v`, where the norm of `e`, a power of the idempotent, is `1`.
    simpa [e, adeleNorm_finAdeleIncl, hv] using congrArg (adeleNorm K L · v) e_mul

/-- If every component of the finite idele `y` of `L` is a unit of the local integers, that is, `y`
is in `idelesUnitOff ∅`, then every component of its norm to `K` has valuation `1`. -/
lemma v_adeleNorm_eq_one {y : (𝔸f L)ˣ} (hy : y ∈ idelesUnitOff ∅)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Valued.v (adeleNorm K L y.val v) = 1 := by
  -- `y` is a unit of `Ô L`, and the norm maps `y` and `y⁻¹` into `Ô K`.
  have h_unit : y.map (adeleNorm K L) ∈ (Ô K).units :=
    (idelesUnitOff_empty.le hy).imp adeleNorm_mem_Ô adeleNorm_mem_Ô
  exact mem_idelesUnitOff.1 (idelesUnitOff_empty.ge h_unit) v (Set.notMem_empty v)

variable [IsCMField K] [IsCMField L]

/-- For an extension `L / K` of CM fields, the norm `adeleNorm K L` of finite adeles commutes with
complex conjugation, written `star`. -/
@[simp]
lemma adeleNorm_star (z : 𝔸f L) : adeleNorm K L (star z) = star (adeleNorm K L z) := by
  -- conjugation on both rings of adeles is compatible with the inclusion, so it respects the norm
  rw [norm_eq_of_equiv_equiv starRingAut starRingAut (RingHom.ext (adeleMap_star _)) (star z)]
  simp [RingEquiv.symm_apply_eq]

/-- For CM fields the norm of finite ideles commutes with conjugation. -/
lemma units_map_adeleNorm_star (w : (𝔸f L)ˣ) :
    map (adeleNorm K L) (star w) = star (w.map (adeleNorm K L)) := Units.ext (adeleNorm_star w.val)

end New

end AdeleNorm

/-!
## Preservation of the module by the norm, and local norms

* `New.norm_localNorm`, `New.v_localNorm`: for an idele with one component `y` at `w`
  (`New.locIdele`), the norm at the place below has absolute value `‖y‖` and valuation `v y ^ f`,
  where `f` is the residue degree.

The local statements follow from the global one, which rests on the product formula and the
finiteness of the class group.
-/

section NormAbsValue

open NumberField WithZeroMulInt FinitePlace Algebra Valued HeightOneSpectrum

namespace New

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {w : FinPlace L}

/-- The norm from `L` to `K` keeps the module `New.finIdeleAbs`, the product of the normalised
absolute values of the components, of a finite idele. -/
lemma finIdeleAbs_adeleNorm (y : (𝔸f L)ˣ) :
    finIdeleAbs (Units.map (adeleNorm K L) y) = finIdeleAbs y := by
  -- The class number `n` is not zero, and `y ^ n` is a principal idele times an idele `u` whose
  -- components are units of the local integers; both sides are nonnegative and multiplicative.
  obtain ⟨_, ⟨x, rfl⟩, u, hu, hxu⟩ := Subgroup.mem_sup.1 (pow_classNumber_mem_principal_sup y)
  have h_map : Units.map (adeleNorm K L) (principalIdele x) = principalIdele (x.map (norm K)) :=
    Units.ext (adeleNorm_algebraMap K L x.val)
  -- `u` and its norm have valuation one at every place
  have h_abs_u : finIdeleAbs u = 1 := ideleAbs_finIdeleIncl_eq_one hu
  have h_abs_norm_u : finIdeleAbs (Units.map (adeleNorm K L) u) = 1 := by
    simp [finIdeleAbs_apply, norm_def, v_adeleNorm_eq_one hu]
  refine (pow_left_inj₀ ideleAbs_pos.le ideleAbs_pos.le (classNumber_ne_zero L)).1 ?_
  calc finIdeleAbs (.map (adeleNorm K L) y) ^ classNumber L
    _ = finIdeleAbs (principalIdele (x.map (norm K))) := by
      simp [← map_pow, ← hxu, h_map, h_abs_norm_u]
    -- the module of `x` is `|N x|⁻¹` (product formula), and norms are transitive
    _ = finIdeleAbs (principalIdele x * u) := by simp [Algebra.norm_norm, h_abs_u]
    _ = finIdeleAbs y ^ classNumber L := by rw [hxu, map_pow]

/-- The local norm from `L_w` to the completion of `K` at the place below `w` keeps the normalised
absolute value. -/
@[simp]
lemma norm_localNorm (y : (LocField w)ˣ) : ‖(localNorm K w y).val‖ = ‖y.val‖ := by
  -- apply `finIdeleAbs_adeleNorm` to the idele supported at `w`; its norm is supported at the place
  -- below
  simp [← finIdeleAbs_locIdele, ← adeleNorm_locIdele, finIdeleAbs_adeleNorm]

/-- Let `f` be the residue degree of `w` over `K`, that is, the residue field orders satisfy
`(w.below K).q ^ f = w.q`. The norm of the idele that is `y` at `w` and `1` elsewhere has
valuation `v y ^ f` at the place below `w` (valuations are written multiplicatively). -/
lemma v_localNorm {f : ℕ} (hf : (w.below K).q ^ f = w.q) (y : (LocField w)ˣ) :
    v (localNorm K w y).val = v y.val ^ f := by
  -- The absolute value at a place is its valuation read in base `q`, and `w.q` is the `f`-th power
  -- of the `q` below; so this is `norm_localNorm`.
  refine (toNNReal_strictMono (one_lt_absNorm_nnreal (w.below K))).injective (NNReal.eq ?_)
  simpa [norm_def, toNNReal_neg_apply, ← hf, ← zpow_natCast, zpow_comm] using norm_localNorm y

end New

end NormAbsValue
