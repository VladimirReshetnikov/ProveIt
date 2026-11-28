import Lib.ClassField.Global.NormTheorems
import Lib.GaloisRep.Main.SelmerModules

/-!
# CM fields: complex conjugation, invariant ideles and splitting characters

This file treats a CM field `L` over its maximal real subfield `L⁺`. The chosen complex conjugation
`c = New.cmConj` of `Ω` acts on the Galois group `Gal(Ω/E)` of a CM field `E` by `g ↦ c g c`, and on
the places of `Ω`.

## Main definitions and results

* `New.Cohomology.upsilon_eq_quadraticIdeleChar`: on the ideles fixed by conjugation (the ideles of
  `L⁺`), a splitting character is the quadratic character `η` of `L/L⁺`
  (`New.Cohomology.quadraticIdeleChar`), which is `1` on the ideles `a z z̄` with `a = ā`
  (`New.Cohomology.IsRealTimesNorm`) and `-1` on the others.
* `New.nonempty_splittingChar`: a splitting character exists when `E` contains a primitive 5040-th
  root of unity and every root of unity of `E` is `δ / δ̄` for a unit `δ` of `𝓞 E` with
  `∏ w, Φ w δ = 1`.
* `New.artinMap_star`, `New.IsPlaceOver.conjPlace_star`, `New.IsFrob.conjPlace_conjGal`,
  `New.conjGal_mem_inertiaGroup_iff`: conjugation is compatible with the Artin map, places,
  Frobenius elements and inertia.
* `New.IsFromU1.apply_idOrConjInv`, `New.IsFromU1.eq_one_of_mem_decompGroup`,
  `New.IsFromU1.eq_one_of_mem_inertiaAbove`: a character `χ` with `χ (Art x) = η (x / x̄)`
  (`New.IsFromU1 S I χ`) is invariant under `g ↦ (c g c)⁻¹`, trivial on decomposition groups above
  `S` and unramified outside `I` and its conjugates.

Notions from other files:
* `New.SplittingChar L`: a unitary Hecke character `υ` of `L` with `υ x̄ = (υ x)⁻¹` that is
  `∏ τ, x_τ / |x_τ|` on the ideles whose finite part is a unit; `υ.atUniformizer w` is its value at
  the chosen uniformiser at the finite place `w`.
* `New.Ω`: an algebraic closure of `ℚ`; the fields `E` with a Galois group `Gal(Ω/E)` carry an
  embedding in it (`New.EmbeddedNumberField`).
* `New.IsFromU1 S I χ`: `χ` is locally constant and `χ (Art x) = η (x / x̄)` for a character `η` of
  the finite ideles that is trivial on `Eˣ` and on the ideles that are units off `S ∪ S̄` and `≡ 1`
  at the places of `I` off `S ∪ S̄`.

## Relation to the literature

Known result: Type A₀ Hecke characters and extension of a CM field's quadratic character. The
results on `New.IsFromU1` concern characters of the norm-one torus of a CM field that are tamely
ramified off `S ∪ S̄`. A splitting character extends the quadratic character and is everywhere
unramified of weight one; such an extension exists under the hypotheses of
`New.nonempty_splittingChar`, but not for every CM field. Source: A. Weil, On a certain type of
characters of the idèle-class group of an algebraic number-field, Tokyo–Nikko symposium 1955 (1956);
exposition A. Raghuram, Notes on the arithmetic of Hecke L-functions, arXiv:2207.03399, §4.

See also `Lib.ClassField.Global.AlbertBrauerHasseNoether` and `Lib.ClassField.Places.LocalFields`.
-/

/-!
## Invariant ideles and splitting characters at inert places

Here `L⁺ = maximalRealSubfield L`, `star` (written `z ↦ z̄`) is complex conjugation on `L`, its
finite adeles `𝔸f L` and its places, `New.CMType` chooses an embedding `Φ w` for each infinite
place `w`, `New.principalIdele` is the diagonal map to the finite ideles, `adeleNorm K L` is the
norm of finite adeles from `L` to `K`, and `finAdeleIncl K L` is base change of finite adeles from
`K` to `L`. For a character `χ` of `Gal(Ω/L⁺)`, `abelianLift χ (artinMap _ b)` is its value at
the Artin symbol of the finite idele `b`, and `IsProGalois (ker χ) L Ω` says that `χ` cuts out
`L`: its kernel is `Gal(Ω/L)`. Finally `0 < c` for `c : ℂ` means that `c` is a positive real
number.
-/

namespace New.Cohomology

open NumberField InfinitePlace Complex ComplexOrder Finset QZChar IsCMField IsTotallyReal
  SplittingChar Units Algebra FinPlace Function

section CMField

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/-- The norm to `L⁺` of a finite adele `y` of `L`, seen in the adeles of `L`, is `y ȳ`. -/
lemma finAdeleIncl_adeleNorm_eq_mul_star (y : 𝔸f L) :
    finAdeleIncl (maximalRealSubfield L) L (adeleNorm (maximalRealSubfield L) L y) =
      y * star y := by
  -- Both sides are continuous in `y` and agree on the dense subring `L`.
  have h_on_L (a : L) :
      finAdeleIncl (maximalRealSubfield L) L (adeleNorm (maximalRealSubfield L) L (a : 𝔸f L)) =
        (a : 𝔸f L) * star (a : 𝔸f L) := by
    simp [norm_maximalRealSubfield_eq_mul_star, Subfield.algebraMap_ofSubfield]
  exact denseRange_algebraMap_finAdele.eq
    (f := fun y ↦ finAdeleIncl (maximalRealSubfield L) L (adeleNorm (maximalRealSubfield L) L y))
    (g := fun y ↦ y * star y) h_on_L (x := y)

/-- A property of the identity and of complex conjugation holds on all of `Gal(L/L⁺)`, which has
these two elements only. -/
lemma gal_maximalReal_induction {P : Gal(L/maximalRealSubfield L) → Prop} (h_one : P 1)
    (h_conj : P (complexConj L)) (σ : Gal(L/maximalRealSubfield L)) : P σ := by
  classical
  have h_cases : σ = 1 ∨ σ = complexConj L := by
    simpa [← pair_complexConj_eq_univ] using mem_univ σ
  rcases h_cases with rfl | rfl
  · exact h_one
  · exact h_conj

/-- Base change of finite ideles from `L⁺` to `L` sends `x` times the norm of `z` to `x z z̄`. -/
lemma map_finAdeleIncl_principalIdele_mul_adeleNorm (x : (maximalRealSubfield L)ˣ) (z : (𝔸f L)ˣ) :
    Units.map (finAdeleIncl (maximalRealSubfield L) L).toMonoidHom
        (principalIdele x * z.map (adeleNorm (maximalRealSubfield L) L)) =
      principalIdele (x.map (maximalRealSubfield L).subtype) * (z * star z) := by
  ext1
  simp [finAdeleIncl_adeleNorm_eq_mul_star, Subfield.algebraMap_ofSubfield]

/-- Galois descent: a finite idele `t` of `L` with `t̄ = t` comes from a finite idele of `L⁺`. -/
lemma exists_map_finAdeleIncl_eq_of_star_eq {t : (𝔸f L)ˣ} (ht : star t.val = t.val) :
    ∃ b : (𝔸f (maximalRealSubfield L))ˣ,
      Units.map (finAdeleIncl (maximalRealSubfield L) L).toMonoidHom b = t := by
  have h_one : ((1 : Gal(L/maximalRealSubfield L)) : L →+* L) = RingHom.id L :=
    RingHom.ext fun _ ↦ rfl
  have h_conj : (complexConj L : L →+* L) = starRingEnd L := RingHom.ext fun _ ↦ rfl
  have h_fixed (σ : Gal(L/maximalRealSubfield L)) : adeleMap (σ : L →+* L) t.val = t.val := by
    induction σ using gal_maximalReal_induction
    · rw [h_one, adeleMap_id]
    · rw [h_conj, ← star_eq_adeleMap, ht]
  -- the inverse of `t` is fixed by the Galois group too, so both come from adeles of `L⁺`
  have h_fixed_inv (σ : Gal(L/maximalRealSubfield L)) :
      adeleMap (σ : L →+* L) t⁻¹.val = t⁻¹.val := by
    apply t.mul_right_inj.mp
    rw [t.mul_inv, ← h_fixed σ, ← map_mul, t.mul_inv, map_one]
  obtain ⟨b, hb⟩ := mem_range_finAdeleIncl_iff.mpr h_fixed
  obtain ⟨c, hc⟩ := mem_range_finAdeleIncl_iff.mpr h_fixed_inv
  have hbc : b * c = 1 := adeleMap_injective (algebraMap (maximalRealSubfield L) L)
    (by rw [map_mul, hb, hc, t.mul_inv, map_one])
  exact ⟨mkOfMulEqOne b c hbc, ext hb⟩

/-- For an embedding of `L` in `Ω`, some character `χ` of `Gal(Ω/L⁺)` cuts out `L`: its kernel is
`Gal(Ω/L)`. -/
lemma exists_char_isProGalois_ker [Algebra L Ω] :
    ∃ χ : QZChar Gal(Ω/maximalRealSubfield L), IsProGalois (ker χ) L Ω :=
  exists_isProGalois_ker_of_isCyclic (isQuadraticExtension L).isCyclic

/-- Let `χ` cut out `L` over `L⁺`, and let `w = w̄` be a finite place of `L`. Then `χ` does not kill
all local Artin symbols at the place of `L⁺` below `w`, as this place does not split in `L`. -/
lemma exists_abelianLift_artinAt_ne_one [Algebra L Ω] {χ : QZChar Gal(Ω/maximalRealSubfield L)}
    [IsProGalois (ker χ) L Ω] {w : FinPlace L} (hw : star w = w) :
    ∃ x : (LocField (w.below (maximalRealSubfield L)))ˣ,
      abelianLift χ (artinAt Gal(Ω/maximalRealSubfield L) (w.below (maximalRealSubfield L)) x) ≠
        1 := by
  let K : Subfield L := maximalRealSubfield L
  by_contra! h_local
  have h_place : IsPlaceOver (placeOver (w.below K)) (w.below K) :=
    (w.below K).isPlaceOver_placeOver
  have h_dec : decompGroup Gal(Ω/K) (placeOver (w.below K)) ≤ ker χ :=
    (h_place.artinAt_trivial_iff_decompGroup_le χ).mp h_local
  -- then `w.below K` splits in `L`, and no nontrivial element of `Gal(L/K)` fixes `w`
  obtain ⟨-, h_no_fix : ∀ σ : Gal(L/K), σ ≠ 1 → w.comap (σ : L →+* L) ≠ w⟩ :=
    h_place.q_eq_and_comap_ne_self_of_decompGroup_le h_dec w rfl
  exact h_no_fix (complexConj L) (complexConj_ne_one L) hw

end CMField

section CMTypeField

variable {L : Type} [Field L] [CMType L]

/-- Restricted to `L⁺`, the embeddings of the CM type are all the complex embeddings of `L⁺`,
each once. -/
lemma bijective_cmType_restrict :
    Bijective fun w : InfinitePlace L ↦ (Φ w).comp (maximalRealSubfield L).subtype := by
  -- Followed by `mk`, this is the bijection from the infinite places of `L` to those of `L⁺`; and
  -- `mk` is injective on the embeddings of `L⁺`, which are all real.
  have h_inj : Injective fun φ : maximalRealSubfield L →+* ℂ ↦ mk φ :=
    LeftInverse.injective fun φ ↦ embedding_mk_eq_of_isReal (complexEmbedding_isReal φ)
  have h_comp : (fun φ : maximalRealSubfield L →+* ℂ ↦ mk φ) ∘
      (fun w : InfinitePlace L ↦ (Φ w).comp (maximalRealSubfield L).subtype) =
        ⇑(equivInfinitePlace L) := by
    funext w
    rw [Function.comp_apply, ← comap_mk, mk_Φ]
    rfl
  refine .of_comp_left ?_ h_inj
  rw [h_comp]
  exact (equivInfinitePlace L).bijective

/-- For any signs `r w = ±1` at the infinite places `w` of `L`, there is a nonzero `a ∈ L⁺` such
that `r (mk φ) * φ a` is a positive real number for every complex embedding `φ` of `L` (weak
approximation for the signs of `L⁺`). -/
lemma exists_maximalRealSubfield_sign_eq (r : InfinitePlace L → ℤˣ) :
    ∃ a : (maximalRealSubfield L)ˣ, ∀ φ : L →+* ℂ, 0 < r (InfinitePlace.mk φ) * φ a.val := by
  -- Take the trace of a `y ∈ L` whose real parts have these signs.
  obtain ⟨y, hy⟩ : ∃ y : L, ∀ w : InfinitePlace L, 0 < r w * (Φ w y).re := by
    let V : Set (InfinitePlace L → ℂ) := Set.univ.pi fun w ↦ {c : ℂ | 0 < r w * c.re}
    have h_open : IsOpen V := isOpen_set_pi Set.finite_univ fun w _ ↦
      isOpen_lt continuous_zero (continuous_re.const_mul (r w))
    have h_mem : (fun w ↦ (r w : ℂ)) ∈ V := by simp [V]
    obtain ⟨y, hy⟩ : ∃ y : L, RingHom.pi Φ y ∈ V := denseRange_Φ.exists_mem_open h_open ⟨_, h_mem⟩
    exact ⟨y, fun w ↦ hy w (Set.mem_univ w)⟩
  have h_sign (φ : L →+* ℂ) :
      0 < r (InfinitePlace.mk φ) * φ (trace (maximalRealSubfield L) L y) := by
    -- `φ` is `Φ (mk φ)` or its conjugate, and the trace is `y + ȳ`
    have h_re : (φ y).re = (Φ (InfinitePlace.mk φ) y).re := by
      rcases Φ_mk_eq_or_star_eq φ with h_eq | h_eq <;> simp [← RingHom.congr_fun h_eq y]
    have h_pos : 0 < r (InfinitePlace.mk φ) * (φ y).re := by
      simpa [h_re] using hy (InfinitePlace.mk φ)
    simpa [trace_maximalRealSubfield_eq_add_star, lt_def, field] using h_pos
  have h_trace_ne : trace (maximalRealSubfield L) L y ≠ 0 := fun h_zero ↦ by
    simp [h_zero] at h_sign
  exact ⟨.mk0 _ h_trace_ne, h_sign⟩

section Character

variable [Algebra L Ω]

/-- The sign law for a CM field `L` with an embedding into `Ω`, the algebraic closure of `ℚ`. If
the character `χ` of `Gal(Ω/L⁺)` cuts out `L`, then it kills the Artin symbol of `b ∈ (L⁺)ˣ`
exactly when `∏ w, Φ w b` is positive. -/
lemma abelianLift_artinMap_eq_one_iff_prod_pos {χ : QZChar Gal(Ω/maximalRealSubfield L)}
    [IsProGalois (ker χ) L Ω] (b : (maximalRealSubfield L)ˣ) :
    abelianLift χ (artinMap Gal(Ω/maximalRealSubfield L) (principalIdele b)) = 1 ↔
      0 < ∏ w : InfinitePlace L, Φ w (b.val : L) := by
  -- `χ` kills no complex conjugation, as `L` is totally complex, so it kills the symbol of `b`
  -- iff the norm of `b` to `ℚ` is positive (`abelianLift_artinMap_principalIdele_eq_one_iff`)
  have hχ_conj (c : Gal(Ω/maximalRealSubfield L)) (hc : IsComplexConj c) : χ.val c ≠ 0 :=
    fun h_zero ↦ hc.false_of_isTotallyComplex (c := (⟨c, h_zero⟩ : ker χ))
  -- `w ↦ Φ w` runs through the embeddings of `L⁺`, so the product is the norm of `b`
  have h_prod : ∏ w : InfinitePlace L, Φ w (b.val : L) =
      ∏ φ : maximalRealSubfield L →ₐ[ℚ] ℂ, φ b.val :=
    ((RingHom.equivRatAlgHom (maximalRealSubfield L) ℂ).bijective.comp
      bijective_cmType_restrict).prod_comp fun φ ↦ φ b.val
  simp [h_prod, abelianLift_artinMap_principalIdele_eq_one_iff hχ_conj, lt_def,
    ← norm_eq_prod_embeddings]

/-- Let `L` be a CM field with an embedding into `Ω`, the algebraic closure of `ℚ`, and `χ` a
character of `Gal(Ω/L⁺)` that cuts out `L`. Let `b` be a finite idele of `L⁺`, and let `s w = ±1`
be signs whose product is `1` exactly when `χ` kills the Artin symbol of `b`. Then `b` is `x` times
a norm from `L`, where `x ∈ (L⁺)ˣ` has the signs `s`. -/
lemma exists_sign_eq_principalIdele_mul_adeleNorm {χ : QZChar Gal(Ω/maximalRealSubfield L)}
    [IsProGalois (ker χ) L Ω] {b : (𝔸f (maximalRealSubfield L))ˣ} {s : InfinitePlace L → ℤˣ}
    (hs : abelianLift χ (artinMap Gal(Ω/maximalRealSubfield L) b) = 1 ↔
      ∏ w : InfinitePlace L, s w = 1) :
    ∃ (x : (maximalRealSubfield L)ˣ) (y : (𝔸f L)ˣ),
      (∀ φ : L →+* ℂ, 0 < s (mk φ) * φ x.val) ∧
        b = principalIdele x * y.map (adeleNorm (maximalRealSubfield L) L) := by
  -- The kernel of `f = χ ∘ artinMap` has index two and consists of the totally positive elements
  -- times norms.
  let K : Subfield L := maximalRealSubfield L
  let f : (𝔸f K)ˣ →* Multiplicative QZ := (abelianLift χ).comp (artinMap Gal(Ω/K))
  have h_index : f.ker.index = 2 :=
    (index_ker_abelianLift_comp_artinMap χ).trans (isQuadraticExtension L).finrank_eq_two
  obtain ⟨a, ha_sign⟩ := exists_maximalRealSubfield_sign_eq s
  -- by the sign law `f a = 1 ↔ f b = 1`, so `b / a` lies in `f.ker`
  have h_prod : 0 < (∏ w, s w : ℤˣ) * ∏ w : InfinitePlace L, Φ w (a.val : L) := by
    simpa [mk_Φ, prod_mul_distrib] using univ.prod_pos fun w _ ↦ ha_sign (Φ w)
  have h_sign_iff : ∏ w, s w = 1 ↔ 0 < ∏ w : InfinitePlace L, Φ w (a.val : L) := by
    rcases Int.units_eq_one_or (∏ w, s w) with h_one | h_neg
    · simpa [h_one] using h_prod
    · have h_prod_neg : ∏ w : InfinitePlace L, Φ w (a.val : L) < 0 := by simpa [h_neg] using h_prod
      simpa [h_neg] using lt_asymm h_prod_neg
  have h_mem_ker : b * principalIdele a⁻¹ ∈ f.ker := by
    rw [f.ker.mul_mem_iff_of_index_two h_index, map_inv, inv_mem_iff]
    exact (hs.trans h_sign_iff).trans (abelianLift_artinMap_eq_one_iff_prod_pos a).symm
  obtain ⟨x, z, hx_pos, hxz⟩ := (abelianLift_artinMap_eq_one_iff χ _).mp h_mem_ker
  refine ⟨a * x, z, fun φ ↦ ?_, by simp [mul_assoc, ← hxz]⟩
  -- `x` is totally positive, so `a * x` has the signs of `a`
  have hφx_pos : 0 < φ (x.val : L) := by
    simpa using zero_lt_real.mpr (hx_pos (complexEmbedding_isReal (φ.comp K.subtype)).embedding)
  simpa [mul_assoc] using mul_pos (ha_sign φ) hφx_pos

end Character

/-- Every finite idele of `L⁺` is an element of `(L⁺)ˣ` times a norm from `L`. -/
lemma exists_eq_principalIdele_mul_adeleNorm (b : (𝔸f (maximalRealSubfield L))ˣ) :
    ∃ (x : (maximalRealSubfield L)ˣ) (y : (𝔸f L)ˣ),
      b = principalIdele x * y.map (adeleNorm (maximalRealSubfield L) L) := by
  algebraize [Ω.fieldEmb L]
  obtain ⟨χ, hχ⟩ := exists_char_isProGalois_ker (L := L)
  -- take signs of product `1` if `χ` kills the symbol of `b`, and of product `-1` otherwise
  obtain ⟨s, hs⟩ : ∃ s : InfinitePlace L → ℤˣ,
      abelianLift χ (artinMap Gal(Ω/maximalRealSubfield L) b) = 1 ↔ ∏ w, s w = 1 := by
    by_cases hb : abelianLift χ (artinMap Gal(Ω/maximalRealSubfield L) b) = 1
    · exact ⟨1, by simp [hb]⟩
    · exact ⟨Pi.mulSingle Classical.ofNonempty (-1), by simp [hb]⟩
  obtain ⟨x, y, -, hxy⟩ := exists_sign_eq_principalIdele_mul_adeleNorm hs
  exact ⟨x, y, hxy⟩

/-- A finite idele `t` of `L` with `t̄ = t` is `x z z̄` with `x ∈ Lˣ` and `z` a finite idele. -/
lemma exists_eq_principalIdele_mul_mul_star_of_star_eq {t : (𝔸f L)ˣ} (ht : star t.val = t.val) :
    ∃ (x : Lˣ) (z : (𝔸f L)ˣ), t = principalIdele x * (z * star z) := by
  -- `t` is the base change of a finite idele `b` of `L⁺`, and `b` is `x` times a norm
  obtain ⟨b, hb⟩ := exists_map_finAdeleIncl_eq_of_star_eq ht
  obtain ⟨x, y, hxy⟩ := exists_eq_principalIdele_mul_adeleNorm b
  refine ⟨x.map (maximalRealSubfield L).subtype, y, ?_⟩
  rw [← hb, hxy, map_finAdeleIncl_principalIdele_mul_adeleNorm]

/-- Given signs `s w = ±1` of product `1`, there are `x ∈ Lˣ` and a finite idele `z` with
`x z z̄ = 1` such that every `φ x` is real with the sign that `s` gives to the place of `φ`. -/
lemma exists_sign_principalIdele_mul_norm_eq_one {s : InfinitePlace L → ℤˣ}
    (hs : ∏ w : InfinitePlace L, s w = 1) :
    ∃ (x : Lˣ) (z : (𝔸f L)ˣ),
      (∀ φ : L →+* ℂ, 0 < s (mk φ) * φ x.val) ∧ principalIdele x * (z * star z) = 1 := by
  algebraize [Ω.fieldEmb L]
  obtain ⟨χ, hχ⟩ := exists_char_isProGalois_ker (L := L)
  -- `χ` kills the Artin symbol of the idele `1` of `L⁺`
  have hs_one : abelianLift χ (artinMap Gal(Ω/maximalRealSubfield L) 1) = 1 ↔
      ∏ w : InfinitePlace L, s w = 1 := by
    simpa using hs
  obtain ⟨x, y, hx_sign, hxy⟩ := exists_sign_eq_principalIdele_mul_adeleNorm hs_one
  have h_one : principalIdele (x.map (maximalRealSubfield L).subtype) * (y * star y) = 1 := by
    rw [← map_finAdeleIncl_principalIdele_mul_adeleNorm, ← hxy, map_one]
  exact ⟨_, y, hx_sign, h_one⟩

/-- If `a ∈ Lˣ` has `ā = a` and `a z z̄ = 1` for a finite idele `z`, then `∏ w, Φ w a` is
positive. -/
lemma prod_Φ_pos_of_principalIdele_mul_norm_eq_one {a : Lˣ} {z : (𝔸f L)ˣ}
    (ha : star a.val = a.val) (haz : principalIdele a * (z * star z) = 1) :
    0 < ∏ w : InfinitePlace L, Φ w a.val := by
  let K : Subfield L := maximalRealSubfield L
  algebraize [Ω.fieldEmb L]
  obtain ⟨χ, hχ⟩ : ∃ χ : QZChar Gal(Ω/K), IsProGalois (ker χ) L Ω := exists_char_isProGalois_ker
  -- `a` comes from `a₀ ∈ Kˣ`, and `a₀` times the norm of `z` is `1`, as base change is injective
  have h_mem : a.val ∈ K := mem_maximalRealSubfield_iff_star_eq.mpr ha
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : Kˣ, a₀.map K.subtype = a :=
    ⟨mk0 ⟨a.val, h_mem⟩ (by simp [Subtype.ext_iff]), ext rfl⟩
  have h_one : principalIdele a₀ * z.map (adeleNorm K L) = 1 := by
    apply map_injective (f := (finAdeleIncl K L).toMonoidHom) (adeleMap_injective _)
    rw [map_finAdeleIncl_principalIdele_mul_adeleNorm, haz, map_one]
  -- `χ` kills norms, so it kills the symbol of `a₀`
  have h_symbol : abelianLift χ (artinMap Gal(Ω/K) (principalIdele a₀)) = 1 := by
    simpa using congrArg (fun y ↦ abelianLift χ (artinMap Gal(Ω/K) y)) h_one
  exact (abelianLift_artinMap_eq_one_iff_prod_pos a₀).mp h_symbol

/-! ### The restriction of a splitting character to the ideles of the real subfield -/

section Restriction

open ComplexConjugate

variable {E : Type} [Field E] [CMType E]

variable (E) in
/-- The idele `x` of `E` lies in `F^× N(𝔸_E^×)`, for the maximal real subfield `F` of `E`: it
is `a z z̄` for an element `a` of `E^×` fixed by conjugation and an idele `z` of `E`. Here
`a.map toAdele` is `a` as a principal idele, and `star` is complex conjugation. -/
def IsRealTimesNorm (x : (𝔸 E)ˣ) : Prop :=
  ∃ (a : Eˣ) (z : (𝔸 E)ˣ), star (a : E) = a ∧ x = a.map (toAdele (E := E)) * (z * star z)

open scoped Classical in
variable (E) in
/-- The quadratic character `η` of `E/F`, for the maximal real subfield `F` of `E`. The ideles of
`F` are the ideles of `E` fixed by conjugation; `η` is `1` on `F^× N(𝔸_E^×)` and `-1` on the other
ideles of `F`. Its values at ideles of `E` that conjugation moves are not used. At a finite place
`w = w̄`, `η` is `-1` at some finite idele `t` fixed by conjugation that is `1` at the other finite
places and at infinity (`exists_quadraticIdeleChar_eq_neg_one`). -/
noncomputable def quadraticIdeleChar (x : (𝔸 E)ˣ) : ℂ :=
  if IsRealTimesNorm E x then 1 else -1

private lemma val_fst_apply_ne_zero (x : (𝔸 E)ˣ) (w : InfinitePlace E) : (x : 𝔸 E).1 w ≠ 0 := by
  have h_mul : (x : 𝔸 E).1 w * ((x⁻¹ : (𝔸 E)ˣ) : 𝔸 E).1 w = 1 :=
    congrFun (congrArg Prod.fst x.mul_inv) w
  exact left_ne_zero_of_mul_eq_one h_mul

/-- Let `w = w̄` be a finite place of `E`, above the place `v` of the maximal real subfield `F`. The
quadratic character `η` of `E/F` is not trivial on `F_v^×`: it is `-1` at some finite idele `t` that
is fixed by conjugation and has the component `1` at all finite places other than `w`. Here
`finIdeleIncl t` is the idele with finite part `t` and components `1` at infinity.

This is part of the local description of `η` in class field theory: non-triviality at a non-split
finite place only, without identifying the kernel on `F_v^×` with the local norms. -/
lemma exists_quadraticIdeleChar_eq_neg_one {w : FinPlace E} (hw : star w = w) :
    ∃ t : (𝔸f E)ˣ, star (finIdeleIncl t) = finIdeleIncl t ∧
      (∀ u : FinPlace E, u ≠ w → t.val u = 1) ∧ quadraticIdeleChar E (finIdeleIncl t) = -1 := by
  -- Let `χ` cut out `E` over `K = F`, and let `x ∈ F_v^×` have a symbol that `χ` does not kill.
  let K : Subfield E := maximalRealSubfield E
  algebraize [Ω.fieldEmb E]
  obtain ⟨χ, hχ⟩ := exists_char_isProGalois_ker (L := E)
  obtain ⟨x, hx⟩ : ∃ x : (LocField (w.below K))ˣ,
      abelianLift χ (artinAt Gal(Ω/K) (w.below K) x) ≠ 1 :=
    exists_abelianLift_artinAt_ne_one hw
  -- `t` is the base change of the idele of `x`; only `w` lies above `w.below K`
  let t : (𝔸f E)ˣ := Units.map (finAdeleIncl K E).toMonoidHom (locIdele (w.below K) x)
  have ht_star : star t.val = t.val := by
    have h_mem : t.val ∈ Set.range (finAdeleIncl K E) := ⟨(locIdele (w.below K) x).val, rfl⟩
    exact mem_range_finAdeleIncl_iff.mp h_mem (complexConj E)
  have ht_star_idele : star (finIdeleIncl t) = finIdeleIncl t :=
    Units.ext (Prod.ext (star_one _) ht_star)
  suffices h_not : ¬ IsRealTimesNorm E (finIdeleIncl t) by
    refine ⟨t, ht_star_idele, fun u hu ↦ ?_, by rw [quadraticIdeleChar, ite_eq_right h_not]⟩
    have h_below : u.below K ≠ w.below K := by
      intro h_eq
      obtain ⟨σ, rfl⟩ : ∃ σ : Gal(E/K), w.comap (σ : E →+* E) = u := exists_gal_comap_eq h_eq.symm
      induction σ using gal_maximalReal_induction
      · exact hu rfl
      · exact hu hw
    show finAdeleIncl K E (locIdele (w.below K) x).val u = 1
    rw [adeleMap_apply _ rfl, locIdele_apply_of_ne h_below, map_one]
  -- If `t = a z z̄`, then `a` is positive at infinity, and `χ` kills the symbol of `x`: that of
  -- `a` by the sign law, and that of a norm.
  rintro ⟨a, z, ha, h_eq⟩
  have h_mem : a.val ∈ K := mem_maximalRealSubfield_iff_star_eq.mpr ha
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : Kˣ, a₀.map K.subtype = a :=
    ⟨mk0 ⟨a.val, h_mem⟩ (by simp [Subtype.ext_iff]), ext rfl⟩
  have h_pos (τ : InfinitePlace E) : 0 < Φ τ (a₀.val : E) := by
    have h_inf : (1 : ℂ) = Φ τ (a₀.val : E) * ((z : 𝔸 E).1 τ * star ((z : 𝔸 E).1 τ)) :=
      congrFun (congrArg (fun y : (𝔸 E)ˣ ↦ (y : 𝔸 E).1) h_eq) τ
    rw [eq_inv_of_mul_eq_one_left h_inf.symm, _root_.inv_pos]
    exact mul_star_self_pos (IsRegular.of_ne_zero (val_fst_apply_ne_zero z τ))
  let y : (𝔸f E)ˣ := z.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  have h_fin : locIdele (w.below K) x = principalIdele a₀ * y.map (adeleNorm K E) := by
    apply map_injective (f := (finAdeleIncl K E).toMonoidHom) (adeleMap_injective _)
    rw [map_finAdeleIncl_principalIdele_mul_adeleNorm]
    exact Units.ext (congrArg (fun y : (𝔸 E)ˣ ↦ (y : 𝔸 E).2) h_eq)
  have h_symbol : abelianLift χ (artinMap Gal(Ω/K) (principalIdele a₀)) = 1 :=
    (abelianLift_artinMap_eq_one_iff_prod_pos a₀).mpr (prod_pos fun τ _ ↦ h_pos τ)
  apply hx
  rw [← artinMap_locIdele, h_fin, map_mul, map_mul, h_symbol, abelianLift_artinMap_adeleNorm,
    mul_one]

/-- If `a z z̄` is fixed by conjugation, for `a ∈ E^×` and a finite idele `z`, then so is `a`. -/
lemma star_eq_of_star_principalIdele_mul_norm {a : Eˣ} {z : (𝔸f E)ˣ}
    (h_star : star (principalIdele a * (z * star z)) = principalIdele a * (z * star z)) :
    star (a : E) = a := by
  -- Conjugation fixes the norm `z z̄`, a unit, which then cancels.
  have h_alg : algebraMap E (𝔸f E) (star (a : E)) * ↑(z * star z) =
      algebraMap E (𝔸f E) a * ↑(z * star z) := by
    simpa [mul_comm] using congrArg Units.val h_star
  exact (algebraMap E (𝔸f E)).injective ((Units.mul_left_inj (z * star z)).mp h_alg)

/-- A splitting character `υ` is `1` on the ideles `a z z̄` of `IsRealTimesNorm`: it is trivial
on `E^×`, and `υ(z̄) = υ(z)⁻¹`. -/
lemma upsilon_eq_one_of_isRealTimesNorm [SplittingChar E] {x : (𝔸 E)ˣ}
    (hx : IsRealTimesNorm E x) : υ.val x = 1 := by
  obtain ⟨a, z, -, rfl⟩ := hx
  rw [map_mul, map_mul, υ_star, mul_inv_cancel, mul_one, upsilon_toAdele]

/-- If a real number `t` has the sign `s = ±1`, then `t / |t| = s` in `ℂ`. -/
private lemma ofReal_div_norm_eq_of_sign {t : ℝ} {s : ℤˣ} (h_sign : 0 < ((s : ℤ) : ℝ) * t) :
    (t : ℂ) / ‖(t : ℂ)‖ = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp_all [abs_of_pos, ne_of_gt]
  · simp_all [abs_of_neg, ne_of_lt]

/-- Let `r` be an idele of `E` with real components at infinity and finite part `1`, on which the
splitting character `υ` is `1`. Then the signs `s w` of its components at infinity have product
`1`. -/
private lemma exists_signs_of_upsilon_eq_one [SplittingChar E] {r : (𝔸 E)ˣ}
    (h_real : ∀ w : InfinitePlace E, (((r : 𝔸 E).1 w).re : ℂ) = (r : 𝔸 E).1 w)
    (hr_fin : (r : 𝔸 E).2 = 1) (h_one : υ.val r = 1) :
    ∃ s : InfinitePlace E → ℤˣ, ∏ w : InfinitePlace E, s w = 1 ∧
      ∀ w : InfinitePlace E, 0 < ((s w : ℤ) : ℝ) * ((r : 𝔸 E).1 w).re := by
  let s : InfinitePlace E → ℤˣ := fun w ↦ if 0 < ((r : 𝔸 E).1 w).re then 1 else -1
  have h_r_sign (w : InfinitePlace E) : 0 < ((s w : ℤ) : ℝ) * ((r : 𝔸 E).1 w).re := by
    have h_ne : ((r : 𝔸 E).1 w).re ≠ 0 := fun h_zero ↦
      val_fst_apply_ne_zero r w (by rw [← h_real w, h_zero, ofReal_zero])
    rcases h_ne.lt_or_gt with h_neg | h_pos
    · simp [s, h_neg.not_gt, h_neg]
    · simp [s, h_pos]
  have h_mem : r.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ (Ô E).units := by
    convert one_mem (Ô E).units
    exact Units.ext hr_fin
  -- `υ_unit` computes `υ(r) = 1` as the product of the signs
  have h_prod : ∏ w : InfinitePlace E, ((s w : ℤ) : ℂ) = 1 :=
    calc ∏ w : InfinitePlace E, ((s w : ℤ) : ℂ)
        = ∏ w : InfinitePlace E, (r : 𝔸 E).1 w / ‖(r : 𝔸 E).1 w‖ :=
          prod_congr rfl fun w _ ↦ by
            simpa [h_real] using (ofReal_div_norm_eq_of_sign (h_r_sign w)).symm
      _ = (υ.val r : ℂ) := (υ_unit r h_mem).symm
      _ = 1 := by rw [h_one, Circle.coe_one]
  refine ⟨s, Units.ext ?_, h_r_sign⟩
  push_cast
  exact_mod_cast h_prod

/-- Let `r` be an idele of `E` fixed by conjugation (an idele of the maximal real subfield), with
finite part `1`, on which the splitting character `υ` is `1`. Then `r = b v v̄` for some `b ∈ E^×`
fixed by conjugation and some idele `v` (`IsRealTimesNorm`). -/
lemma isRealTimesNorm_of_finPart_eq_one [SplittingChar E] {r : (𝔸 E)ˣ} (hr : star r = r)
    (hr_fin : (r : 𝔸 E).2 = 1) (h_one : υ.val r = 1) : IsRealTimesNorm E r := by
  -- The components of `r` at infinity are real, and `υ(r) = 1` is the product of their signs.
  -- Some `b ∈ E^×` fixed by conjugation has these signs, and `r / b` is `v v̄` for the idele `v`
  -- with the square roots of the positive reals `r_w / b_w` at infinity.
  have h_real (w : InfinitePlace E) : (((r : 𝔸 E).1 w).re : ℂ) = (r : 𝔸 E).1 w := by
    have h_conj : conj ((r : 𝔸 E).1 w) = (r : 𝔸 E).1 w := by
      simpa using congrFun (congrArg (fun y : (𝔸 E)ˣ ↦ (y : 𝔸 E).1) hr) w
    exact conj_eq_iff_re.mp h_conj
  obtain ⟨s, h_prod, h_r_sign⟩ := exists_signs_of_upsilon_eq_one h_real hr_fin h_one
  -- some `b ∈ E^×` has the signs `s`, and `b u ū = 1` for a finite idele `u`
  obtain ⟨b, u, h_signs, h_u⟩ := exists_sign_principalIdele_mul_norm_eq_one h_prod
  have hb : star (b : E) = b :=
    star_eq_of_star_principalIdele_mul_norm (z := u) (by rw [h_u, star_one])
  have h_b_real (w : InfinitePlace E) : ((Φ w b).re : ℂ) = Φ w b :=
    conj_eq_iff_re.mp (by rw [starRingEnd_apply, ← map_star_complex, hb])
  have h_b_sign (w : InfinitePlace E) : 0 < ((s w : ℤ) : ℝ) * (Φ w b).re := by
    simpa [mk_Φ] using (pos_iff.mp (h_signs (Φ w))).1
  have h_ratio_pos (w : InfinitePlace E) : 0 < ((r : 𝔸 E).1 w).re / (Φ w b).re := by
    simpa [mul_div_mul_left] using div_pos (h_r_sign w) (h_b_sign w)
  -- `r = b v v̄`, with `v` the square roots of `r / b` at infinity and `u` at the finite places
  let q (w : InfinitePlace E) : ℝ := √(((r : 𝔸 E).1 w).re / (Φ w b).re)
  have hq_ne (w : InfinitePlace E) : (q w : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (h_ratio_pos w))
  let v : 𝔸 E := (fun w ↦ (q w : ℂ), (u : 𝔸f E))
  have hv : IsUnit v :=
    Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w ↦ (hq_ne w).isUnit, u.isUnit⟩
  have h_inf (w : InfinitePlace E) :
      (r : 𝔸 E).1 w = Φ w b * ((q w : ℂ) * conj (q w : ℂ)) := by
    have h_ne_b : (Φ w b).re ≠ 0 := right_ne_zero_of_mul (h_b_sign w).ne'
    rw [conj_ofReal, ← ofReal_mul, Real.mul_self_sqrt (h_ratio_pos w).le]
    nth_rw 1 [← h_real w, ← h_b_real w]
    rw [← ofReal_mul, mul_div_cancel₀ _ h_ne_b]
  refine ⟨b, hv.unit, hb, Units.ext (Prod.ext (funext h_inf) ?_)⟩
  show (r : 𝔸 E).2 = algebraMap E (𝔸f E) b * ((u : 𝔸f E) * star (u : 𝔸f E))
  rw [hr_fin]
  exact congrArg Units.val h_u.symm

/-- Let `υ` be a splitting character of the CM field `E`: a unitary Hecke character with
`υ x̄ = (υ x)⁻¹` that equals `∏ x_τ / |x_τ|` on ideles whose finite part is a unit of `Ô`. Let `x`
be an idele of `E` fixed by conjugation (an idele of the maximal real subfield) with `υ x = 1`. Then
`x = a z z̄` for some `a ∈ E^×` fixed by conjugation and some idele `z` of `E`
(`IsRealTimesNorm`). -/
lemma isRealTimesNorm_of_upsilon_eq_one [SplittingChar E] {x : (𝔸 E)ˣ} (hx : star x = x)
    (h_one : υ.val x = 1) : IsRealTimesNorm E x := by
  -- The finite part of `x` is `a z z̄` with `a ∈ E^×` fixed by conjugation. Divided by
  -- `y = a z z̄`, `x` leaves an idele fixed by conjugation with finite part `1`.
  let finPart : (𝔸 E)ˣ →* (𝔸f E)ˣ := Units.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  have h_fin_star : star (finPart x : 𝔸f E) = finPart x := by
    simpa [finPart] using congrArg (fun y : (𝔸 E)ˣ ↦ (y : 𝔸 E).2) hx
  obtain ⟨a, z, h_t⟩ := exists_eq_principalIdele_mul_mul_star_of_star_eq h_fin_star
  have ha : star (a : E) = a :=
    star_eq_of_star_principalIdele_mul_norm (z := z) (by rw [← h_t]; exact Units.ext h_fin_star)
  let ζ : (𝔸 E)ˣ := finIdeleIncl z
  let y : (𝔸 E)ˣ := a.map (toAdele (E := E)) * (ζ * star ζ)
  have hy : IsRealTimesNorm E y := ⟨a, ζ, ha, rfl⟩
  have hy_star : star y = y := Units.ext (by simp [y, ζ, ha, mul_comm])
  have hr_star : star (x / y) = x / y := by
    rw [div_eq_mul_inv, star_mul, star_inv, hx, hy_star, mul_comm]
  have hr_fin : finPart (x / y) = 1 := by
    rw [map_div, div_eq_one, h_t]
    exact Units.ext (by simp [y, ζ, finPart])
  have hr_one : υ.val (x / y) = 1 := by
    rw [map_div, h_one, upsilon_eq_one_of_isRealTimesNorm hy, div_one]
  obtain ⟨b, ρ, hb, h_r⟩ : IsRealTimesNorm E (x / y) :=
    isRealTimesNorm_of_finPart_eq_one hr_star (congrArg Units.val hr_fin) hr_one
  refine ⟨b * a, ρ * ζ, by simp [hb, ha], ?_⟩
  calc x = x / y * y := (div_mul_cancel x y).symm
    _ = (b * a).map (toAdele (E := E)) * (ρ * ζ * star (ρ * ζ)) := by
      rw [h_r]
      apply Units.ext
      simp only [y, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.coe_star, map_mul,
        star_mul']
      ring

/-- On an idele `x` of `E` fixed by conjugation, that is, an idele of the maximal real subfield
`F`, a splitting character `υ` equals the quadratic character `η` of `E/F`
(`quadraticIdeleChar`). -/
theorem upsilon_eq_quadraticIdeleChar [SplittingChar E] {x : (𝔸 E)ˣ} (hx : star x = x) :
    (υ.val x : ℂ) = quadraticIdeleChar E x := by
  -- `υ(x)² = υ(x) υ(x̄) = 1`, so `υ(x) = ±1`; and `υ(x) = 1` exactly on `F^× N(𝔸_E^×)`.
  have h_sq : (υ.val x : ℂ) * υ.val x = 1 := by
    have h_mul_star : υ.val x * υ.val (star x) = 1 := by rw [υ_star, mul_inv_cancel]
    rw [hx] at h_mul_star
    exact_mod_cast congrArg (fun c : Circle ↦ (c : ℂ)) h_mul_star
  by_cases h_mem : IsRealTimesNorm E x
  · simp [quadraticIdeleChar, h_mem, upsilon_eq_one_of_isRealTimesNorm h_mem]
  · have h_ne : (υ.val x : ℂ) ≠ 1 := fun h_one ↦
      h_mem (isRealTimesNorm_of_upsilon_eq_one hx (Circle.ext (h_one.trans Circle.coe_one.symm)))
    rw [quadraticIdeleChar, ite_eq_right h_mem]
    exact (mul_self_eq_one_iff.mp h_sq).resolve_left h_ne

/-- Let `E` be a CM field with a CM type, and let `υ` be a splitting character of `E`. That is, `υ`
is a unitary Hecke character with `υ x̄ = (υ x)⁻¹`, and it equals `∏ x_τ / |x_τ|` on ideles whose
finite part is a unit of `Ô`. If `w` is a finite place of `E` with `star w = w` and `ϖ ∈ E_w^×` has
valuation `exp(-1)` (a uniformiser), then `υ` takes the value `-1` on `locFullIdele w ϖ`, the idele
that is `ϖ` at `w` and `1` at every other place. -/
theorem upsilon_locFullIdele_eq_neg_one_of_star_eq [SplittingChar E] (w : FinPlace E)
    (ϖ : (LocField w)ˣ) (hw : star w = w) (hϖ : Valued.v (ϖ : LocField w) = WithZero.exp (-1)) :
    (υ.val (locFullIdele w ϖ) : ℂ) = -1 := by
  -- `υ` is `η` on the ideles fixed by conjugation, so it is `-1` at some `t` that is `1` off `w`.
  obtain ⟨t, ht_star, ht_one, ht⟩ := exists_quadraticIdeleChar_eq_neg_one hw
  have h_value : (υ.val (finIdeleIncl t) : ℂ) = -1 := by
    rw [upsilon_eq_quadraticIdeleChar ht_star, ht]
  -- As `υ` is unramified, its value at `ϖ` is `υ.atUniformizer w`, whose square is `1`, and its
  -- value at `t` is a power of this number.
  have h_ϖ : (υ.val (locFullIdele w ϖ) : ℂ) = υ.atUniformizer w := by
    rw [upsilon_eq_atUniformizer_zpow w (by simp +contextual [locFullIdele])]
    simp [locFullIdele, hϖ]
  have h_sq : υ.atUniformizer w * υ.atUniformizer w = 1 := by
    simpa [hw] using upsilon_atUniformizer_mul_star w
  have h_unit (u : FinPlace E) (hu : u ≠ w) : Valued.v ((finIdeleIncl t).val.2 u) = 1 :=
    (congrArg Valued.v (ht_one u hu)).trans (map_one Valued.v)
  rw [h_ϖ]
  refine (mul_self_eq_one_iff.mp h_sq).resolve_left fun h_one ↦ ?_
  norm_num [upsilon_eq_atUniformizer_zpow w h_unit, h_one] at h_value

/-- A splitting character is `-1` at the chosen uniformiser at a finite place `w = w̄`. -/
lemma upsilon_atUniformizer_eq_neg_one [SplittingChar E] (w : FinPlace E) (hw : star w = w) :
    υ.atUniformizer w = -1 :=
  upsilon_locFullIdele_eq_neg_one_of_star_eq w (uniformizer w) hw (v_uniformizer w)

/-- The four properties of a splitting character `υ` of `E` that are used: (1) `υ(ȳ) = υ(y)⁻¹`;
(2) `υ(y) = ∏_τ y_τ/|y_τ|` over the infinite places `τ` if the finite part of `y` is a unit of
`Ô E`; (3) `υ(ϖ) = -1` for every uniformiser `ϖ` at a finite place `w = w̄`, placed at `w` in an
idele by `locFullIdele`; (4) on the ideles fixed by conjugation, the ideles of the maximal real
subfield `F`, `υ` is the quadratic character `η` of `E/F`. This collects `υ_star`, `υ_unit`,
`upsilon_locFullIdele_eq_neg_one_of_star_eq` and `upsilon_eq_quadraticIdeleChar`. -/
theorem υ_star_eq_inv_and_apply_eq [SplittingChar E] :
    (∀ y : (𝔸 E)ˣ, υ.val (star y) = (υ.val y)⁻¹) ∧
    (∀ y : (𝔸 E)ˣ, y.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ (Ô E).units →
      (υ.val y : ℂ) = ∏ w : InfinitePlace E, (y : 𝔸 E).1 w / ‖(y : 𝔸 E).1 w‖) ∧
    (∀ (w : FinPlace E) (ϖ : (LocField w)ˣ), star w = w →
      Valued.v (ϖ : LocField w) = WithZero.exp (-1) → (υ.val (locFullIdele w ϖ) : ℂ) = -1) ∧
    ∀ y : (𝔸 E)ˣ, star y = y → (υ.val y : ℂ) = quadraticIdeleChar E y :=
  ⟨υ_star, υ_unit, upsilon_locFullIdele_eq_neg_one_of_star_eq,
    fun _ hy ↦ upsilon_eq_quadraticIdeleChar hy⟩

end Restriction

end CMTypeField

end New.Cohomology

/-!
## Existence of a splitting character

`New.nonempty_splittingChar` constructs a splitting character `New.SplittingChar E` of a CM field
`E` that contains a primitive 5040-th root of unity (`New.HasPrimitiveRoot5040`) and in which every
root of unity is `δ / δ̄` for a unit `δ` of `𝓞 E` with `∏ w, Φ w δ = 1`.

The adeles `New.𝔸 E` have one factor `ℂ` for each infinite place, in which `E` is embedded by the
chosen embedding `Φ w` of `New.CMType`.
-/

section SplittingCharExists

open NumberField Units Finset Complex ComplexOrder Embeddings New.Cohomology Circle Function
  Submonoid

/-- Suppose that every root of unity of `E` is `δ / δ̄` for a unit `δ` of `𝓞 E` with
`∏ w, Φ w δ = 1`. Let `x = y b b̄` for `y ∈ E^×` and an idele `b` of `E`, where the finite part
of `x` is a unit at every finite place. Then `∏_w x_w / |x_w| = 1`, over the infinite places `w`. -/
private lemma New.prod_div_norm_eq_one_of_mem_idelesUnitOff {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E]
    (hE : ∀ y : E, IsOfFinOrder y → ∃ δ : (𝓞 E)ˣ,
      ∏ w : InfinitePlace E, Φ w (δ : E) = 1 ∧ y * star (δ : E) = δ)
    {y : Eˣ} {b x : (𝔸 E)ˣ} (hx_eq : Units.map toAdele.toMonoidHom y * (b * star b) = x)
    (hx_unit : x.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ idelesUnitOff ∅) :
    ∏ w : InfinitePlace E, (x : 𝔸 E).1 w / ‖(x : 𝔸 E).1 w‖ = 1 := by
  -- `y` and `ȳ` have the same valuations, so `ȳ / y` is a root of unity, `δ / δ̄` by `hE`. Then
  -- `a = y δ` is real and the finite part of `a b b̄` is a norm, so `∏ Φ w a > 0` by class field
  -- theory for `E/E⁺`. As `b b̄ > 0` at infinity and `∏ Φ w δ = 1`, the product is
  -- `∏ Φ w a / |∏ Φ w a| = 1`.
  rw [← hx_eq] at hx_unit
  have h_val (w : FinPlace E) : w.valuation E (y : E) *
      (Valued.v ((b : 𝔸 E).2 w) * Valued.v ((b : 𝔸 E).2 (star w))) = 1 := by
    simpa using mem_idelesUnitOff.mp hx_unit w (Set.notMem_empty w)
  -- `ȳ / y` is an algebraic integer whose conjugates all have absolute value 1, so a root of unity
  have h_int : IsIntegral ℤ (star (y : E) / y) := by
    refine algebraMap_mem_Ô.mp (mem_Ô.mpr fun w ↦ ?_)
    have h_star : w.valuation E (star (y : E)) *
        (Valued.v ((b : 𝔸 E).2 (star w)) * Valued.v ((b : 𝔸 E).2 w)) = 1 := by
      simpa using (v_star_apply _ w).trans
        (mem_idelesUnitOff.mp hx_unit (star w) (Set.notMem_empty (star w)))
    suffices h_ratio : w.valuation E (star (y : E)) / w.valuation E (y : E) ≤ 1 by
      simpa using h_ratio
    rw [eq_inv_of_mul_eq_one_left h_star, eq_inv_of_mul_eq_one_left (h_val w), mul_comm]
    exact div_self_le_one _
  obtain ⟨n, hn_pos, h_pow⟩ := pow_eq_one_of_norm_eq_one E ℂ h_int fun φ ↦ by simp
  obtain ⟨δ, hδ_prod, h_yδ⟩ := hE _ (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn_pos, h_pow⟩)
  -- `a = y δ` is real, and the finite part of `a b b̄`, a real unit, is a norm `t̄ t`
  let a : Eˣ := mk0 ((y : E) * δ) (by simp)
  have ha_real : star (a : E) = a := by simpa [a, field] using h_yδ
  let u : 𝔸f E := (toAdele (a : E) * (b * star b)).2
  have h_fin_star : star u = u := by simp [u, ha_real, mul_comm]
  have h_fin_unit (w : FinPlace E) : Valued.v (u w) = 1 := by
    simpa [u, a, w.valuation_eq_one_iff_notMem.mpr, w.asIdeal.notMem_of_isUnit] using h_val w
  obtain ⟨t, ht⟩ := exists_unit_star_mul_self_eq h_fin_star h_fin_unit
  -- So `a z z̄ = 1` for the finite idele `z = b / t`, which forces `0 < ∏ Φ w a`
  let z : (𝔸f E)ˣ :=
    b.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)) / t.map (Ô E).subtype.toMonoidHom
  have h_az : principalIdele a * (z * star z) = 1 := by
    rw [star_div, div_mul_div_comm, mul_div, div_eq_one, Units.ext_iff, eq_comm, mul_comm]
    exact ht
  have h_pos : 0 < ∏ w : InfinitePlace E, Φ w (a : E) :=
    prod_Φ_pos_of_principalIdele_mul_norm_eq_one ha_real h_az
  -- each factor is that of `Φ w y`, as `b_w b̄_w = ‖b_w‖² > 0`; and `∏ Φ w y = ∏ Φ w a`
  have h_factor (w : InfinitePlace E) :
      (x : 𝔸 E).1 w / ‖(x : 𝔸 E).1 w‖ = Φ w (y : E) / ‖Φ w (y : E)‖ := by
    have hb : (b : 𝔸 E).1 w ≠ 0 := val_fst_apply_ne_zero b w
    simp [← hx_eq, mul_conj', field]
  have h_prod_a : ∏ w : InfinitePlace E, Φ w (a : E) = ∏ w : InfinitePlace E, Φ w (y : E) := by
    simp [a, prod_mul_distrib, hδ_prod]
  calc _ = ∏ w : InfinitePlace E, Φ w (y : E) / ‖Φ w (y : E)‖ := prod_congr rfl fun w _ ↦ h_factor w
    _ = (∏ w : InfinitePlace E, Φ w (a : E)) / ‖∏ w : InfinitePlace E, Φ w (a : E)‖ := by
      rw [prod_div_distrib, h_prod_a, norm_prod, ofReal_prod]
    _ = 1 := by rw [norm_of_nonneg' h_pos.le, div_self h_pos.ne']

/-- Let `E` be a CM field with a CM type `Φ` (a complex embedding `Φ w` inducing each infinite place
`w`) that contains a primitive 5040-th root of unity (`New.HasPrimitiveRoot5040`). Suppose every
root of unity `y` of `E` (written `IsOfFinOrder y`) equals `δ / δ̄` for some unit `δ` of `𝓞 E` with
`∏ w, Φ w δ = 1`. Then `E` has a splitting character (`New.SplittingChar`), that is, a unitary Hecke
character `υ` of `E` with `υ x̄ = (υ x)⁻¹` that equals `∏ x_τ / |x_τ|` (over the infinite places) on
ideles whose finite part is a unit of `Ô`. -/
lemma New.nonempty_splittingChar {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E]
    (hE : ∀ y : E, IsOfFinOrder y → ∃ δ : (𝓞 E)ˣ,
      ∏ w : InfinitePlace E, Φ w (δ : E) = 1 ∧ y * star (δ : E) = δ) :
    Nonempty (SplittingChar E) := by
  -- Let `S x = ∏ x_w / |x_w|`, `U` the ideles that are units at all finite places, and `R` the
  -- group of the `y b b̄` with `y ∈ Eˣ`. Once `S = 1` on `U ∩ R`, the restriction of `S` to `U`
  -- extends to a character of the ideles that is trivial on `R`, as the circle is divisible.
  have h_ne (x : (𝔸 E)ˣ) (w : InfinitePlace E) : (x : 𝔸 E).1 w ≠ 0 := val_fst_apply_ne_zero x w
  -- `S` lies on the unit circle, is multiplicative and is continuous
  let phase (x : (𝔸 E)ˣ) : ℂ := ∏ w : InfinitePlace E, (x : 𝔸 E).1 w / ‖(x : 𝔸 E).1 w‖
  have h_phase_mem (x : (𝔸 E)ˣ) : phase x ∈ Submonoid.unitSphere ℂ := by
    simp [phase, Submonoid.unitSphere, prod_eq_zero_iff, h_ne]
  have h_phase_mul (x y : (𝔸 E)ˣ) : phase (x * y) = phase x * phase y := by
    simp [phase, mul_div_mul_comm, prod_mul_distrib]
  have h_phase_cont : Continuous fun x : (𝔸 E)ˣ ↦ (⟨phase x, h_phase_mem x⟩ : Circle) := by
    fun_prop (disch := aesop)
  let S : (𝔸 E)ˣ →ₜ* Circle :=
    ⟨.mk' (fun x ↦ ⟨phase x, h_phase_mem x⟩) fun x y ↦ Subtype.ext (h_phase_mul x y), h_phase_cont⟩
  let U : Subgroup (𝔸 E)ˣ :=
    (idelesUnitOff ∅).comap (Units.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)))
  let R : Subgroup (𝔸 E)ˣ :=
    ((Units.map toAdele.toMonoidHom).coprod (MonoidHom.id (𝔸 E)ˣ * starMulAut.toMonoidHom)).range
  have h_glue (x : (𝔸 E)ˣ) (hU : x ∈ U) (hR : x ∈ R) : S x = 1 := by
    obtain ⟨⟨y, b⟩, hx_eq : Units.map toAdele.toMonoidHom y * (b * star b) = x⟩ := hR
    have h_phase : phase x = 1 := New.prod_div_norm_eq_one_of_mem_idelesUnitOff hE hx_eq hU
    exact Circle.ext (h_phase.trans Circle.coe_one.symm)
  let h_divisible : DivisibleBy (Additive Circle) ℤ :=
    Surjective.divisibleBy (fun t : ℝ ↦ .ofMul (exp t)) exp_surjective exp_zsmul
  obtain ⟨υ, hυR, hυ⟩ : ∃ υ : (𝔸 E)ˣ →* Circle, R ≤ υ.ker ∧ ∀ x : U, υ x = S x :=
    exists_monoidHom_extend U.subtype (S.domRestrict U) R fun x hR ↦ h_glue x x.property hR
  -- `υ` is continuous because it agrees with `S` on the open subgroup `U`.
  have h_open : IsOpen (U : Set (𝔸 E)ˣ) :=
    (isOpen_idelesUnitOff ∅).preimage (continuous_snd.units_map _)
  have hυU : Set.EqOn υ S U := fun x hx ↦ hυ ⟨x, hx⟩
  have h_cont : Continuous υ := continuous_of_continuousAt_one υ
    (h_open.continuousOn_iff.mp (S.continuous.continuousOn.congr hυU) U.one_mem)
  -- `υ` is trivial on `Eˣ ≤ R`, equals `S` on `U`, and `υ x * υ x̄ = 1`, as `x x̄ ∈ R`.
  refine ⟨{ υ := ⟨⟨υ, h_cont⟩, ?_⟩, υ_unit := fun x hx ↦ ?_, υ_star := fun x ↦ ?_ }⟩
  · -- a principal idele `x = y` lies in `R`, as the image of `(y, 1)`
    rintro x ⟨y, hy⟩
    have hy_ne : y ≠ 0 := fun hy_zero ↦ x.ne_zero (by simp [← hy, hy_zero])
    have hx_mem : x ∈ R := ⟨(Units.mk0 y hy_ne, 1), Units.ext (by simpa using hy)⟩
    exact MonoidHom.mem_ker.mp (hυR hx_mem)
  · exact congrArg ((↑) : Circle → ℂ) (hυU (idelesUnitOff_empty.ge hx))
  · have h_mem : x * star x ∈ R := ⟨(1, x), by simp⟩
    exact eq_inv_of_mul_eq_one_right ((map_mul υ x (star x)).symm.trans (hυR h_mem))

end SplittingCharExists

/-! ## Complex conjugation on the Galois group, places and Artin map; characters from U(1) -/

namespace New

variable {ℓ : ℕ} [ThePrime ℓ]
  {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {A : ClosurePlace} {v : FinPlace E} (b : Bool) (g : Gal(Ω/E))

@[simp, grind =]
lemma star_mem_placesDividing {T : ℕ} : star v ∈ placesDividing E T ↔ v ∈ placesDividing E T := by
  simp [placesDividing]

/-! ### Conjugation on the Galois group and on places -/

/-- The element `g` if `b` is true, and `(conjGal g)⁻¹ = (c g c)⁻¹` if `b` is false. -/
noncomputable def idOrConjInv (b : Bool) (g : Gal(Ω/E)) : Gal(Ω/E) := cond b g (conjGal g)⁻¹

private lemma idOrConjInv_true : idOrConjInv true g = g := rfl

private lemma idOrConjInv_false : idOrConjInv false g = (conjGal g)⁻¹ := rfl

@[simp]
lemma conjGal_conjGal : conjGal (conjGal g) = g := by
  ext
  simp [conjGal]

/-- The chosen complex conjugation `c` intertwines `g^c = c g c` with `g`: `c (g^c x) = g (c x)`. -/
lemma cmConj_conjGal_smul (x : Ω) : cmConj.toRingHom (conjGal g • x) = g • cmConj.toRingHom x :=
  -- by definition `conjGal g • x = c (g (c x))`, and `c (c z) = z`
  cmConj_cmConj _

@[fun_prop]
lemma continuous_conjGal : Continuous (conjGal (E := E)) :=
  continuous_of_equivariant_emb _ cmConj_conjGal_smul

@[simp]
lemma cyclotomicChar_conjGal : cyclotomicChar Ω ℓ (conjGal g) = cyclotomicChar Ω ℓ g :=
  cyclotomicChar_eq_of_equivariant ℓ (cmConj_conjGal_smul g)

/-- The global Artin map of a CM field `E` is compatible with complex conjugation: if the Artin
symbol of the finite idele `x` is the class of `g ∈ Gal(Ω/E)`, then that of the conjugate idele `x̄`
is the class of `conjGal g = c g c`, where `c` is the chosen complex conjugation of `Ω`. -/
lemma artinMap_star {x : (𝔸f E)ˣ} (h : artinMap Gal(Ω/E) x = g) :
    artinMap Gal(Ω/E) (star x) = conjGal g := by
  -- Norm compatibility (`artinMap_map_adeleNorm`) for `E` as an extension of itself through complex
  -- conjugation.
  let h_starAlgebra : Algebra E E := (starRingEnd E).toAlgebra
  have h_art : artinMap Gal(Ω/E) (star (star x)) = g := by rwa [star_star]
  -- `star (star x)` is the image of `star x` and the degree is one, so its norm is `star x`
  have h_incl : ((star (star x) : (𝔸f E)ˣ) : 𝔸f E) = finAdeleIncl E E ((star x : (𝔸f E)ˣ) : 𝔸f E) :=
    rfl
  have h_norm : (star (star x)).map (adeleNorm E E) = star x := by
    rw [Units.ext_iff, Units.coe_map, h_incl, adeleNorm_finAdeleIncl,
      Module.finrank_of_bijective_algebraMap starMulAut.bijective, pow_one]
  rw [← h_norm]
  exact artinMap_map_adeleNorm h_art _ cmConj_algebraMap (cmConj_conjGal_smul g)

/-- The conjugate place: the preimage of the valuation subring A of Ω under the chosen complex
conjugation. -/
noncomputable def conjPlace (A : ClosurePlace) : ValuationSubring Ω := A.comap cmConj.toRingHom

variable {g}

@[simp]
lemma conjPlace_conjPlace : conjPlace (conjPlace A) = A := by
  ext
  simp [conjPlace]

/-- Let E be a CM field. If the valuation subring A of Ω lies over the finite place v of E, then
the conjugate place of A under the chosen complex conjugation lies over the conjugate prime
v̄. -/
lemma IsPlaceOver.conjPlace_star (h : IsPlaceOver A v) : IsPlaceOver (conjPlace A) (star v) := by
  intro x
  have h_conj : cmConj.toRingHom (algebraMap E Ω (x : E)) = algebraMap E Ω (star (x : E)) :=
    cmConj_algebraMap (x : E)
  rw [conjPlace, comap_apply_lt_one_iff, h_conj, mem_star_place]
  exact h (star x)

/-- Conjugation maps a Frobenius element of exponent `q` at the place `A` to one at the conjugate
place. -/
lemma IsFrob.conjPlace_conjGal {q : ℕ} (hg : IsFrob A q g) :
    IsFrob (conjPlace A) q (conjGal g) :=
  map cmConj_conjGal_smul hg

/-- Let E be a CM field, g in Gal(Ω/E) and c the chosen complex conjugation. Then g^c = cgc lies
in the inertia group of the conjugate place of A if and only if g lies in the inertia group
of A. -/
@[simp]
lemma conjGal_mem_inertiaGroup_iff :
    conjGal g ∈ inertiaGroup Gal(Ω/E) (conjPlace A) ↔ g ∈ inertiaGroup Gal(Ω/E) A := by
  -- inertia is the case `q = 1` of `IsFrob.conjPlace_conjGal`; both conjugations are involutions
  refine ⟨fun hg ↦ ?_, IsFrob.conjPlace_conjGal⟩
  have h_frob : IsFrob (conjPlace (conjPlace A)) 1 (conjGal (conjGal g)) :=
    IsFrob.conjPlace_conjGal hg
  rwa [conjPlace_conjPlace, conjGal_conjGal] at h_frob

omit [NumberField.IsCMField E] in
/-- The `ℓ`-adic cyclotomic character is unramified outside `ℓ`: it is `1` at every `g` that lies
in the inertia group of a place of `Ω` above a finite place of `E` not dividing `ℓ`. -/
lemma Selmer.cyclotomicChar_eq_one_of_mem_inertiaAbove
    (hg_inertia : g ∈ inertiaAbove (placesDividing E ℓ)ᶜ) : cyclotomicChar Ω ℓ g = 1 := by
  -- `g` is in the inertia group of a place `B` above a place `u` that does not divide `ℓ`
  obtain ⟨u, hu_not_dvd, B, hB, hg⟩ := hg_inertia
  exact cyclotomicChar_eq_one_of_mem_inertiaGroup ℓ hg
    (hB.valuation_natCast_eq_one_iff.mpr hu_not_dvd)

/-! ### Characters that come from U(1) -/

variable {C : Type*} [CommMonoid C] {S I : Set (FinPlace E)} {χ : Gal(Ω/E) →* C}

/-- Let `χ : Gal(Ω/E) →* C` come from the norm-one torus in the sense of `IsFromU1 S I χ`:
`χ(Art x) = η(x / x̄)` for an idele class character `η` of modulus `I` that is trivial on the local
components at the places of `S` and their conjugates. Then `χ(idOrConjInv b g) = χ(g)` for both
values of the boolean `b`, and in particular `χ((c g c)⁻¹) = χ(g)`. -/
lemma IsFromU1.apply_idOrConjInv (h : IsFromU1 S I χ) (g : Gal(Ω/E)) :
    χ (idOrConjInv b g) = χ g := by
  cases b
  · -- If `g = Art x` then `idOrConjInv false g = Art x̄⁻¹`, and both ideles have the same `x / x̄`.
    obtain ⟨η, -, -, hη⟩ := h.exists_ideleChar
    obtain ⟨x, hx⟩ := artinMap_surjective Gal(Ω/E) g
    have hx_conj : artinMap Gal(Ω/E) (star x)⁻¹ = idOrConjInv false g := by
      simp [idOrConjInv_false, artinMap_star g hx]
    simp [hη x g hx, hη _ _ hx_conj, inv_mul_eq_div]
  · rw [idOrConjInv_true]

/-- Let `S` and `I` be sets of finite places of the CM field `E`, and let `χ` be a character of
`Gal(Ω/E)` with `IsFromU1 S I χ`. This means `χ(Art x) = η(x / x̄)` for an idele class character `η`
of modulus `I` that is trivial on the local components at `S ∪ S̄`. Then `χ` kills the decomposition
groups above `S`: if the place `A` of `Ω` lies over a place `v ∈ S` of `E` and `g` is in the
decomposition group of `A`, then `χ g = 1`. -/
lemma IsFromU1.eq_one_of_mem_decompGroup (h : IsFromU1 S I χ) (hv : v ∈ S)
    (hA : IsPlaceOver A v) (hg : g ∈ decompGroup Gal(Ω/E) A) :
    χ g = 1 := by
  obtain ⟨η, -, hη_one, hχ⟩ := h.exists_ideleChar
  -- The local Artin map has dense range and `χ` is locally constant, so `χ g = χ s` for some `s`
  -- in the decomposition group whose class is the local symbol of some `x`.
  obtain ⟨x, s, hs, hx⟩ : ∃ (x : (LocField v)ˣ) (s : decompGroup Gal(Ω/E) A),
      χ g = χ s ∧ ↑s = localArtin Gal(Ω/E) A v x :=
    hA.denseRange_localArtin.exists_mem_open
      (QuotientGroup.isOpenMap_coe _ (h.isLocallyConstant _).preimage_val) ⟨_, ⟨g, hg⟩, rfl, rfl⟩
  have h_art : artinMap Gal(Ω/E) (locIdele v x) = (s : Gal(Ω/E)) := by
    simp [hA.artinAt_eq_of_localArtin_eq hx.symm]
  rw [hs, hχ _ _ h_art, star_locIdele]
  -- `η` kills the idele `x / x̄`: its components off `v` and `star v`, which both lie in
  -- `S.conjClosure`, are `1`
  have hv_mem : v ∈ S.conjClosure := Or.inl hv
  have h_star_v_mem : star v ∈ S.conjClosure := Or.inr (by simpa using hv)
  have h_at_one (a : (LocField v)ˣ) (a' : (LocField (star v))ˣ) (w : FinPlace E)
      (hw : w ∉ S.conjClosure) : ideleAt w (locIdele v a / locIdele (star v) a') = 1 := by
    rw [map_div, ideleAt_locIdele_of_ne (ne_of_mem_of_not_mem hv_mem hw).symm,
      ideleAt_locIdele_of_ne (ne_of_mem_of_not_mem h_star_v_mem hw).symm, div_one]
  apply hη_one
  · simp +contextual [idelesUnitOff, h_at_one]
  · intro w hw
    simp [h_at_one _ _ w (Set.notMem_of_mem_sdiff hw)]

/-- Let `S` and `I` be sets of finite places of the CM field `E`, and let `χ` be a character of
`Gal(Ω/E)` with `IsFromU1 S I χ`. This means `χ(Art x) = η(x / x̄)` for an idele class character `η`
of modulus `I` that is trivial on the local components at `S ∪ S̄`. Then `χ` kills inertia outside
`I` and its conjugates: `χ g = 1` for `g` in the inertia group of a place of `Ω` above a place of
`E` not in `I ∪ Ī`. -/
lemma IsFromU1.eq_one_of_mem_inertiaAbove (h : IsFromU1 S I χ) (g : Gal(Ω/E))
    (hg_inertia : g ∈ inertiaAbove I.conjClosureᶜ) : χ g = 1 := by
  obtain ⟨v, hv_not_mem, A, hA, hg⟩ := hg_inertia
  obtain ⟨η, -, hη_one, hχ⟩ := h.exists_ideleChar
  -- the class of an inertia element is the local Artin symbol of a unit `x`
  obtain ⟨x, hx_unit, hx⟩ := hA.exists_localArtin_eq_of_mem_inertiaGroup hg
  have h_art : artinMap Gal(Ω/E) (locIdele v x) = g := by simp [hA.artinAt_eq_of_localArtin_eq hx]
  rw [hχ _ _ h_art, star_locIdele]
  -- `η` kills `x / x̄`: it is a unit everywhere, and `1` at the places of `I`, because
  -- `v ∉ I.conjClosure`
  apply hη_one
  · have hx_val : Valued.v (x : LocField v) = 1 := by simpa using hx_unit
    exact div_mem (locIdele_mem_idelesUnitOff hx_val)
      (locIdele_mem_idelesUnitOff (by simpa using hx_val))
  · rintro w ⟨hw_I, -⟩
    have hw_ne_v : w ≠ v := ne_of_mem_of_not_mem hw_I fun hv_I ↦ hv_not_mem (Or.inl hv_I)
    have hw_ne_star_v : w ≠ star v := ne_of_mem_of_not_mem hw_I fun hv_I ↦ hv_not_mem (Or.inr hv_I)
    simp [ideleAt_locIdele_of_ne hw_ne_v, ideleAt_locIdele_of_ne hw_ne_star_v]

end New
