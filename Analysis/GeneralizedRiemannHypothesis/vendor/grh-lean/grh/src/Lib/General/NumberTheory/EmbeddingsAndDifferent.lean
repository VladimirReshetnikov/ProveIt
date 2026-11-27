import Lib.Adelic.Adeles.AdditiveCharacter

/-!
# Embeddings, differents and the maximal real subfield of a CM field

The file collects general lemmas on differents and root discriminants of number fields. It then
compares a CM field `E` with its maximal real subfield E⁺ (`maximalRealSubfield E`), covering the
trace, the norm, the different and the discriminant.

* `star` is complex conjugation on the CM field `E` and on its integers `𝓞 E`.
* `Φ v` is the complex embedding chosen at the infinite place `v`: by `New.PlaceEmbedding` in
  general, and by `New.CMType`, which extends it, for CM fields.
* `New.volÔ E` is `2 ^ r₂ / √|disc E|`, with `r₂` the number of complex places of `E`.

## Main definitions and results

* `New.differentIdeal_eq_span_of_dvd`: a criterion for `f'(x)` to generate the different and for
  `𝓞 L = A[x]`.
* `New.mem_maximalRealSubfield_iff_star_eq`, `New.trace_maximalRealSubfield_eq_add_star`,
  `New.norm_maximalRealSubfield_eq_mul_star`: E⁺ is the fixed field of conjugation, and the trace
  and norm from `E` to E⁺ are `x + x̄` and `x x̄`.
* `New.differentIdeal_eq_top`, `New.abs_discr_eq_discr_maximalRealSubfield_sq`: under
  `New.HasPrimitiveRoot5040` the relative different is trivial and |disc E| = (disc E⁺)².
* `New.volÔ_eq`: the mass `New.volÔ` of the integral finite adeles in terms of the root
  discriminant.
* `New.exists_mixedEquiv_maximalRealSubfield`: the Minkowski space of E⁺ as real functions on the
  infinite places of `E`.
* `New.Variety.prod_embeddings_eq_prod_pairs`: a product over the complex embeddings of a totally
  complex field, grouped into conjugate pairs.
-/

/-! ## Differents and root discriminants -/

namespace New

open NumberField Polynomial Fintype Ideal Module Algebra Real InfinitePlace

variable (K : Type*) {L A : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Let `A` be a Dedekind domain with fraction field `K`, with `𝓞 L` finite over `A`. Let `x ∈ 𝓞 L`
generate `L` over `K`, and let `f` be a polynomial over `A` with root `x`. If `y = f'(x)` generates
an ideal that divides the different of `𝓞 L` over `A`, then `y` generates the different and
`𝓞 L = A[x]`. -/
lemma differentIdeal_eq_span_of_dvd [Algebra K L] [CommRing A] [IsDedekindDomain A] [Algebra A K]
    [IsFractionRing A K] [Algebra A (𝓞 L)] [IsTorsionFree A (𝓞 L)] [Module.Finite A (𝓞 L)]
    [CharZero A] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A (𝓞 L) L] {x y : 𝓞 L}
    (hx : K[(x : L)] = ⊤) (f : A[X]) (hf : aeval x f = 0) (hy : aeval x f.derivative = y)
    (h_dvd : span {y} ∣ differentIdeal A (𝓞 L)) :
    differentIdeal A (𝓞 L) = span {y} ∧ A[x] = ⊤ := by
  -- Let `p` be the minimal polynomial, `𝔠` the conductor and `𝔡` the different. Then
  -- `𝔡 ∣ 𝔠 * 𝔡 = (p'(x)) ∣ (f'(x)) = (y) ∣ 𝔡`, so all these ideals are equal and `𝔠 = 1`.
  obtain ⟨g, rfl⟩ : minpoly A x ∣ f := minpoly.isIntegrallyClosed_dvd (.of_finite A x) hf
  have h_deriv : y = aeval x (minpoly A x).derivative * aeval x g := by simp [← hy]
  have h_mul_dvd : conductor A x * differentIdeal A (𝓞 L) ∣ span {y} := by
    rw [conductor_mul_differentIdeal A K L x hx, h_deriv, ← span_singleton_mul_span_singleton]
    exact dvd_mul_right _ _
  have h_cond : conductor A x * differentIdeal A (𝓞 L) = differentIdeal A (𝓞 L) :=
    (h_mul_dvd.trans h_dvd).antisymm (dvd_mul_left _ _)
  have h_top : conductor A x = ⊤ := by simpa [differentIdeal_ne_bot] using h_cond
  rw [h_cond] at h_mul_dvd
  exact ⟨h_mul_dvd.antisymm h_dvd, conductor_eq_top_iff_adjoin_eq_top.1 h_top⟩

/-- A generator `x` of the different of `𝓞 L` over `ℤ` is nonzero. -/
lemma ne_zero_of_differentIdeal_eq_span {x : 𝓞 L} (hx : differentIdeal ℤ (𝓞 L) = span {x}) :
    x ≠ 0 :=
  fun h_zero ↦ differentIdeal_ne_bot (by simpa [h_zero] using hx)

/-- An ideal `P` of the integers of a number field `L` whose square contains a rational prime `p`
divides the different of `L` over `ℚ`. -/
lemma dvd_differentIdeal_of_mem_sq {P : Ideal (𝓞 L)} {p : ℕ} [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ P ^ 2) : P ∣ differentIdeal ℤ (𝓞 L) := by
  -- If `P ^ e` divides `p 𝓞 L`, then `P ^ (e - 1)` divides the different; take `e = 2`.
  have h_sq_dvd : P ^ 2 ∣ (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 L)) := by simp [map_span, hp]
  simpa using pow_sub_one_dvd_differentIdeal ℤ P 2 (by simp [NeZero.ne]) h_sq_dvd

/-- The number of infinite places of the number field `K`. -/
noncomputable abbrev Core.numInfPlaces : ℕ := card (InfinitePlace K)

lemma finrank_eq_two_mul_card_infinitePlace [IsTotallyComplex K] :
    finrank ℚ K = 2 * Core.numInfPlaces K := by simp [← sum_mult_eq, mul_comm]

/-- The root discriminant `|disc K| ^ (1 / [K : ℚ])` of a totally complex field is positive. -/
lemma rootDiscr_pos [IsTotallyComplex K] : 0 < rootDiscr K :=
  rpow_pos_of_pos (by simp [discr_ne_zero]) _

/-- For a totally complex number field `K` with `r` infinite places and root discriminant `rd`,
the absolute discriminant is `(rd ^ r) ^ 2`. -/
lemma abs_discr_eq_rootDiscr_pow [IsTotallyComplex K] :
    (|NumberField.discr K| : ℝ) = (rootDiscr K ^ Core.numInfPlaces K) ^ 2 := by
  simp [← pow_mul', ← finrank_eq_two_mul_card_infinitePlace, rootDiscr,
    rpow_inv_natCast_pow, finrank_pos.ne']

end New

/-! ## The maximal real subfield: trace, norm, different and discriminant -/

section RealSubfield

open NumberField MeasureTheory Algebra InfinitePlace IsCMField IsTotallyReal Submodule Finset

namespace New

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- The maximal real subfield of a CM field is the fixed field of complex conjugation. -/
lemma mem_maximalRealSubfield_iff_star_eq {x : E} : x ∈ maximalRealSubfield E ↔ star x = x :=
  (complexConj_eq_self_iff E x).symm

open scoped Classical in
/-- The automorphisms of a CM field over its maximal real subfield are the identity and complex
conjugation. -/
lemma pair_complexConj_eq_univ :
    ({1, complexConj E} : Finset (E ≃ₐ[maximalRealSubfield E] E)) = univ :=
  eq_univ_of_card _ <| by rw [card_pair (complexConj_ne_one E).symm, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank, IsQuadraticExtension.finrank_eq_two]

lemma complexConj_apply_eq_star (x : E) : complexConj E x = star x := rfl

/-- The trace from a CM field `E` to its maximal real subfield is `x + x̄`. -/
lemma trace_maximalRealSubfield_eq_add_star (x : E) :
    (trace (maximalRealSubfield E) E x : E) = x + star x := by
  classical
  refine (trace_eq_sum_automorphisms (K := maximalRealSubfield E) x).trans ?_
  rw [← pair_complexConj_eq_univ, sum_pair (complexConj_ne_one E).symm, AlgEquiv.one_apply,
    complexConj_apply_eq_star]

/-- The norm from a CM field `E` to its maximal real subfield is `x * x̄`. -/
lemma norm_maximalRealSubfield_eq_mul_star (x : E) :
    (Algebra.norm (maximalRealSubfield E) x : E) = x * star x := by
  classical
  refine (norm_eq_prod_automorphisms (maximalRealSubfield E) x).trans ?_
  rw [← pair_complexConj_eq_univ, prod_pair (complexConj_ne_one E).symm, AlgEquiv.one_apply,
    complexConj_apply_eq_star]

/-- If `x` lies in the trace dual of the integers of the CM field `E` over those of its maximal
real subfield, then `(y - ȳ) * x` is an algebraic integer for every integer `y` of `E`. -/
lemma isIntegral_sub_star_mul_of_mem_traceDual (y : 𝓞 E) {x : E}
    (hx : x ∈ traceDual (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
      (1 : Submodule (𝓞 E) E)) :
    IsIntegral ℤ ((y - star y : 𝓞 E) * x) := by
  have h_trace (u : 𝓞 E) : IsIntegral ℤ (trace (maximalRealSubfield E) E (x * u) : E) :=
    isIntegral_trans (A := 𝓞 (maximalRealSubfield E)) _
      (mem_traceDual_iff_isIntegral.1 hx u (mem_one.2 ⟨u, rfl⟩)).algebraMap
  have h_eq : (y - star y : 𝓞 E) * x = trace (maximalRealSubfield E) E (x * y) -
      (star y : 𝓞 E) * trace (maximalRealSubfield E) E (x * (1 : 𝓞 E)) := by
    have h_star : ((star y : 𝓞 E) : E) = star (y : E) := by simp
    simp only [trace_maximalRealSubfield_eq_add_star, star_mul', h_star, map_sub, map_one, mul_one]
    ring
  rw [h_eq]
  exact (h_trace y).sub ((star y).isIntegral_coe.mul (h_trace 1))

/-- Let the integers of the CM field `E` contain `i` with `i² = -1`, `ī = -i` and `β` with
`β + β̄ = 1`. Then `E` has trivial different over its maximal real subfield, so it is unramified at
all finite places. -/
lemma differentIdeal_eq_top_of_add_star_eq_one {i β : 𝓞 E} (hi_sq : i * i = -1)
    (hi_star : star i = -i) (hβ : β + star β = 1) :
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
  -- For `y = i β` the number `y - ȳ = i` is a unit. It lies in the different, the inverse of the
  -- trace dual, because it multiplies the trace dual into the integers.
  have h_sub : i * β - star (i * β) = i := by
    rw [star_mul', hi_star]
    linear_combination i * hβ
  have hi_mem : (i : E) ∈
      IsLocalization.coeSubmodule E (differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
    rw [coeSubmodule_differentIdeal _ (maximalRealSubfield E), mem_div_iff_forall_mul_mem]
    intro x hx
    have h_int : IsIntegral ℤ (i * x) := by
      simpa only [h_sub] using isIntegral_sub_star_mul_of_mem_traceDual (i * β) hx
    exact mem_one.2 ⟨⟨i * x, h_int⟩, rfl⟩
  obtain ⟨j, hj_mem, hj_eq⟩ := (IsLocalization.mem_coeSubmodule E _).1 hi_mem
  obtain rfl : j = i := RingOfIntegers.coe_injective hj_eq
  exact Ideal.eq_top_of_isUnit_mem _ hj_mem (.of_mul_eq_one (-j) (by simp [hi_sq]))

/-- A CM field that contains a primitive root of unity of order `5040` has trivial different over
its maximal real subfield. -/
@[simp]
lemma differentIdeal_eq_top [HasPrimitiveRoot5040 E] :
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
  -- the field contains `i` with `i² = -1`, `ī = -i` and `ω` of trace `1` over the real subfield
  obtain ⟨i, ω, hi_sq, hi_star, hω, -⟩ :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  exact differentIdeal_eq_top_of_add_star_eq_one hi_sq hi_star hω

/-- If the CM field `E` contains a primitive root of unity of order `5040`, its discriminant is, up
to sign, the square of that of its maximal real subfield. -/
lemma abs_discr_eq_discr_maximalRealSubfield_sq [HasPrimitiveRoot5040 E] :
    |NumberField.discr E| = NumberField.discr (maximalRealSubfield E) ^ 2 := by
  -- the tower formula for discriminants, with trivial relative different and degree two
  rw [Int.abs_eq_natAbs, natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (maximalRealSubfield E) (𝓞 (maximalRealSubfield E)) E (𝓞 E), differentIdeal_eq_top,
    IsQuadraticExtension.finrank_eq_two]
  simp

/-- The mass `volÔ E = 2 ^ r₂ / √|disc E|` of the integral finite adeles of a CM field `E` is
`(rd / 2) ^ (-r)`, with `rd` the root discriminant of `E` and `r` the number of its infinite
places. -/
lemma volÔ_eq : (volÔ E : ℝ) = ((rootDiscr E / 2) ^ Core.numInfPlaces E)⁻¹ := by
  have h_places : nrComplexPlaces E = Core.numInfPlaces E := by
    simp [card_eq_nrRealPlaces_add_nrComplexPlaces]
  have h_sqrt : √|(NumberField.discr E : ℝ)| = rootDiscr E ^ Core.numInfPlaces E := by
    simp [abs_discr_eq_rootDiscr_pow, (rootDiscr_pos E).le]
  simp [volÔ, Int.norm_eq_abs, h_places, h_sqrt, div_pow]

open scoped Classical in
/-- Let `E` be a CM field with a chosen complex embedding `Φ v` at each infinite place `v`. There is
a measure-preserving real-linear isomorphism from the Minkowski space of the maximal real subfield
E⁺ to the real functions on the infinite places of `E` that sends the image of `a ∈ E⁺` to
`v ↦ Re (Φ v a)`. -/
lemma exists_mixedEquiv_maximalRealSubfield {E : Type*} [Field E] [CMType E] :
    ∃ e : mixedEmbedding.mixedSpace (maximalRealSubfield E) ≃ₗ[ℝ] InfinitePlace E → ℝ,
      MeasurePreserving e ∧
      ∀ a : maximalRealSubfield E,
        e (mixedEmbedding (maximalRealSubfield E) a) =
          fun v : InfinitePlace E ↦ (Φ v (a : E)).re := by
  -- The real subfield has no complex place, so its Minkowski space is the space of real functions
  -- on its real places, and these correspond to the infinite places of `E` by restriction.
  have h_complex : IsEmpty {w : InfinitePlace (maximalRealSubfield E) // w.IsComplex} :=
    Fintype.card_eq_zero_iff.1 (nrComplexPlaces_eq_zero _)
  let σ : InfinitePlace E ≃ {w : InfinitePlace (maximalRealSubfield E) // w.IsReal} :=
    (equivInfinitePlace E).trans (Equiv.subtypeUnivEquiv isReal).symm
  refine ⟨.prodUnique ≪≫ₗ .funCongrLeft ℝ ℝ σ, ?_, fun a ↦ funext fun v ↦ ?_⟩
  · -- dropping the trivial factor and reindexing both preserve the volume
    have h_fst : MeasurePreserving
        (Prod.fst : mixedEmbedding.mixedSpace (maximalRealSubfield E) →
          {w : InfinitePlace (maximalRealSubfield E) // w.IsReal} → ℝ) :=
      ⟨measurable_fst, by simp [volume]⟩
    exact ((volume_measurePreserving_piCongrLeft _ σ).symm _).comp h_fst
  · -- the restriction `φ` of `Φ v` is real, so it is the embedding of the place `σ v` below `v`
    let φ : maximalRealSubfield E →+* ℂ := (Φ v).comp (algebraMap (maximalRealSubfield E) E)
    have h_below : (σ v : InfinitePlace (maximalRealSubfield E)) = .mk φ := by
      simp [φ, σ, ← comap_mk, mk_Φ]
    have h_emb : (σ v : InfinitePlace (maximalRealSubfield E)).embedding = φ := by
      rw [h_below, embedding_mk_eq_of_isReal (complexEmbedding_isReal φ)]
    change embedding_of_isReal (σ v).prop a = (φ a).re
    rw [← h_emb, ← embedding_of_isReal_apply (σ v).prop, Complex.ofReal_re]

end New

end RealSubfield

/-! ## Complex embeddings of a totally complex field in conjugate pairs -/

section Embeddings

open NumberField Polynomial ComplexEmbedding InfinitePlace Finset IsTotallyComplex

namespace New.Variety

@[simp, grind]
lemma conjugate_ne_self {E : Type*} [Field E] [IsTotallyComplex E] (σ : E →+* ℂ) :
    conjugate σ ≠ σ :=
  complexEmbedding_not_isReal _

/-- For a totally complex number field `E`, a product over all complex embeddings is a product over
the infinite places `v` of the factors at the embedding `Φ v` chosen at `v` and at its conjugate. -/
@[to_additive]
lemma prod_embeddings_eq_prod_pairs {E : Type*} [Field E] [IsTotallyComplex E] [NumberField E]
    [PlaceEmbedding E] {M : Type*} [CommMonoid M] (F : (E →+* ℂ) → M) :
    ∏ σ : E →+* ℂ, F σ = ∏ v : InfinitePlace E, F (Φ v) * F (conjugate (Φ v)) := by
  -- Group the embeddings by places: above `v` lie exactly `Φ v` and its conjugate, which differ.
  rw [← prod_fiberwise _ mk F]
  refine prod_congr rfl fun v _ ↦ ?_
  apply prod_eq_mul <;> grind [mk_Φ, mk_eq_iff]

/-- For a polynomial `P` over a totally complex field, the roots of `P` under the conjugate of an
embedding `σ` are the complex conjugates of its roots under `σ`, with multiplicity. -/
lemma roots_map_conjugate {E : Type*} [Field E] [IsTotallyComplex E] (P : E[X]) (σ : E →+* ℂ) :
    (P.map (conjugate σ)).roots = (P.map σ).roots.map star := by
  -- Conjugating the coefficients of a split polynomial conjugates its roots.
  have h_conj : conjugate σ = (starRingEnd ℂ).comp σ := RingHom.ext (conjugate_coe_eq σ)
  simp only [h_conj, ← Polynomial.map_map, (IsAlgClosed.splits (P.map σ)).roots_map,
    starRingEnd_apply]

end New.Variety

end Embeddings
