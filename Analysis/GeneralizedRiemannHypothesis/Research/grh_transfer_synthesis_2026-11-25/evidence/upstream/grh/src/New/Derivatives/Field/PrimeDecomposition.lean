import Lib.ClassField.Places.ValuationSubrings
import New.Reduction.Data.FieldsAndPlaces

/-!
# Different and prime decomposition of the CM field E = K(ζ)

Let `K = ℚ(√-d) ⊆ ℂ` and `E = P.E s = K(ζ)`, with `ζ` a primitive root of unity of order `q₁`.
`star` is complex conjugation on `E`. This file computes the different of `E`, gives it a purely
imaginary generator, and describes how the primes `p ∤ q₁ d` decompose in `E`. The infinite
places `v` of `E` form a group isomorphic to `Gal(E/K)` and to `(ℤ/q₁)ˣ`, and `v • w` is the
pullback of a finite place `w` along the automorphism `P.galOfPlace s v`. In the comments P'(ζ)
stands for `New.Parameters.relDifferentGen`, the value at `ζ` of the derivative of the cyclotomic
polynomial of order `q₁`; this letter P is not the parameters.

## Main definitions and results

* `New.Parameters.deltaE`, `New.Parameters.star_deltaE`,
  `New.Parameters.differentIdeal_eq_span_deltaE`: the imaginary generator of the different of `E`.
* `New.Parameters.smul_eq_iff_exists_frobElem_pow`: for a prime `p ∤ q₁ d` and `w` above `p`, the
  place `v` sends `w` to `w` exactly when `(v, 1)` is a power of the Frobenius element
  `New.Parameters.frobElem` in the monoid `P.Φ s × ℤ`, and to `w̄` exactly when `(v, -1)` is. For
  such `p`, `New.Parameters.q_eq_pow_orderOf_frobElem` gives the norm of `w`.

Notions from other files:
* `New.Parameters`: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a prime `d` with
  `d ≡ q₀/2 - 1 mod q₀`.
* `New.Parameters.q₁`: the number `q₁ = 3 ^ c * 2 ^ s * q₀`, with `c = ⌊log₃ s⌋ + 5`.
* `New.Parameters.Φ`: `P.Φ s` is the group of infinite places of `E`. It is distinct from the bare
  `Φ` of the CM type of `E` (`New.CMType`): `Φ v : E →+* ℂ` is the embedding over `K` inducing `v`.
-/

noncomputable section

namespace New.Parameters

/-!
## Action of automorphisms of ℂ over K on the infinite places of E

An automorphism `σ` of `ℂ` over `K` permutes the embeddings `Φ v` of `E = P.E s` over `K`, which are
indexed by the infinite places `v`.
-/

/-- For an automorphism `σ` of `ℂ` over `K`, the permutation of the infinite places of `E = P.E s`
given by multiplication by the place of the embedding `σ ∘ Φ 1`. Here `Φ v : E →+* ℂ` is the
embedding over `K` chosen at the place `v`, and the places carry the group structure of
`Gal(E/K)` (that of `P.Φ s`). -/
noncomputable def placePerm {P : Parameters} (s : ℕ) (σ : Gal(ℂ/K P)) :
    Equiv.Perm (NumberField.InfinitePlace (P.E s)) :=
  Equiv.mulLeft (NumberField.InfinitePlace.mk (RingHom.comp σ (Φ 1)) : P.Φ s)

lemma placePerm_apply {P : Parameters} {s : ℕ} (σ : Gal(ℂ/P.K)) (v : P.Φ s) :
    placePerm s σ v = (NumberField.InfinitePlace.mk (RingHom.comp σ (Φ 1)) : P.Φ s) * v := rfl

/-- An automorphism `σ` of `ℂ` over `K` carries the embedding `Φ v : E →+* ℂ` chosen at the infinite
place `v` of `E = P.E s` to the embedding chosen at the place `placePerm s σ v`. -/
lemma apply_Phi_eq_Phi_placePerm {P : Parameters} {s : ℕ} {σ : Gal(ℂ/P.K)}
    (v : NumberField.InfinitePlace (P.E s)) (x : P.E s) :
    σ (Φ v x) = Φ (placePerm (P := P) s σ v) x := by
  -- `σ ∘ Φ 1` is an embedding over `K`, so it is `Φ` of the place `v₀` that it induces.
  let φ : P.E s →ₐ[P.K] ℂ := .comp σ ⟨Φ 1, by simp⟩
  let v₀ : P.Φ s := .mk (RingHom.comp σ (Φ 1))
  have h_emb : (⟨Φ v₀, by simp⟩ : P.E s →ₐ[P.K] ℂ) = φ := P.algHom_eq_of_mk_eq s (mk_Φ v₀)
  have h_apply (y : P.E s) : Φ v₀ y = σ (Φ 1 y) := DFunLike.congr_fun h_emb y
  rw [placePerm_apply, phi_mul, h_apply, ← phi_mul, one_mul]

/-!
## The different of E and an imaginary generator

A primitive `q₁`-th root of unity generates `𝓞 E` over `𝓞 K`, and P'(ζ) generates the different of
`E/K`.
-/

section Different

open Ideal Finset IntermediateField IsCyclotomicExtension NumberField Polynomial Algebra
  InfinitePlace RingOfIntegers NeZero QuadField algebraMap

variable {P : Parameters} {s : ℕ} {z : 𝓞 (E P s)}

/-! ### The integers `ζ`, `(1 + √-d) / 2` and `√-d` of `E`, and a root of unity of order `5040` -/

/-- The chosen primitive `q₁`-th root of unity as an element of `𝓞 E`. -/
abbrev zetaInt (P : Parameters) (s : ℕ) : 𝓞 (P.E s) :=
  (isPrimitiveRoot_zeta (P := P) (s := s)).toInteger

@[simp]
lemma coe_zetaInt : P.zetaInt s = P.ζ s := rfl

lemma isPrimitiveRoot_zetaInt : IsPrimitiveRoot (P.zetaInt s) (P.q₁ s) :=
  isPrimitiveRoot_zeta.toInteger_isPrimitiveRoot

/-- The number `β_K = (1 + √-d) / 2` as an integer of `E`. -/
abbrev betaKInE (P : Parameters) (s : ℕ) : 𝓞 (E P s) := betaK P.d

/-- The integer `√-d = 2 β_K - 1` of `K`, as an element of `𝓞 E`. -/
def sqrtNegDInE (P : Parameters) (s : ℕ) : 𝓞 (P.E s) :=
  algebraMap (𝓞 (K P)) (𝓞 (E P s)) (sqrtNegDInt P.d)

/-- The element `√-d` of `𝓞 E` is the image in `E` of `sqrtNegD P.d`, the square root `√-d` in the
quadratic field `QuadField P.d = ℚ(√-d)`, which is `P.K`. -/
@[simp]
lemma coe_sqrtNegDInE :
    (P.sqrtNegDInE s).val = algebraMap (QuadField P.d) (P.E s) (sqrtNegD P.d) := by
  change algebraMap P.K (P.E s) (sqrtNegDInt P.d).val = algebraMap P.K (P.E s) (sqrtNegD P.d)
  simp [two_mul]

lemma star_sqrtNegDInE : star (P.sqrtNegDInE s) = -P.sqrtNegDInE s :=
  ext (by simp [← map_star_CM])

/-- The conjugate of `ζ ^ c` is its inverse in `𝓞 E`, for the root of unity `ζ = zetaInt`. -/
lemma star_zetaInt_pow_mul_zetaInt_pow_eq_one (c : ℕ) :
    star (P.zetaInt s) ^ c * P.zetaInt s ^ c = 1 :=
  ext (by simp [isPrimitiveRoot_zeta.ne_zero, ne])

lemma sqrtNegDInE_sq : P.sqrtNegDInE s ^ 2 = -P.d := by
  rw [sqrtNegDInE, ← map_pow, sqrtNegDInt_sq, map_neg, map_natCast]

lemma sqrtNegDInE_dvd_d : P.sqrtNegDInE s ∣ P.d :=
  ⟨-P.sqrtNegDInE s, by rw [mul_neg, ← sq, sqrtNegDInE_sq, neg_neg]⟩

/-- The different of `K`, extended to `𝓞 E`, is generated by `√-d`. -/
lemma map_differentIdeal_eq_span_sqrtNegDInE :
    (differentIdeal ℤ (𝓞 P.K)).map (algebraMap (𝓞 P.K) (𝓞 (P.E s))) = span {P.sqrtNegDInE s} := by
  rw [(different_eq_span_and_adjoin_betaK P.d).1, map_span, Set.image_singleton, sqrtNegDInE]

/-- `β_K β̄_K = (d + 1) / 4` in `𝓞 E`, with `β̄_K = 1 - β_K`. -/
lemma betaKInE_mul_one_sub (P : Parameters) (s : ℕ) :
    betaKInE P s * (1 - P.betaKInE s) = (((P.d + 1) / 4 : ℕ) : 𝓞 (P.E s)) := by
  simpa using congrArg (algebraMap (𝓞 P.K) (𝓞 (P.E s))) (betaK_mul_one_sub P.d)

/-- `β_K + β̄_K = 1`: the complex conjugate of `β_K` in `𝓞 E` is `1 - β_K`. -/
lemma star_betaKInE (P : Parameters) (s : ℕ) : star (betaKInE P s) = 1 - P.betaKInE s := by
  have h_star : 2 * star (P.betaKInE s) - 1 = -(2 * P.betaKInE s - 1) := by
    simpa [sqrtNegDInE, map_ofNat] using star_sqrtNegDInE (P := P) (s := s)
  exact mul_left_cancel₀ two_ne_zero (by linear_combination h_star)

/-- The field `E` contains a primitive root of unity of order `5040`. -/
instance : HasPrimitiveRoot5040 (P.E s) where
  exists_primitive_root := by
    -- `5040` divides `18480 * 3`, hence `q₁`; take the power `q₁ / 5040` of `ζ`
    have h_three : 3 ∣ towerDeg s := (dvd_pow_self 3 (Nat.succ_ne_zero _)).mul_right _
    have h_dvd : 5040 ∣ P.q₁ s := .trans (by norm_num) (mul_dvd_mul P.dvd_q₀ h_three)
    exact ⟨P.ζ s ^ (P.q₁ s / 5040), isPrimitiveRoot_zeta.pow one_le (Nat.div_mul_cancel h_dvd).symm⟩

/-! ### The different of `E/K` at a primitive `q₁`-th root of unity -/

/-- The derivative of the cyclotomic polynomial of level `q₁`, evaluated at a primitive `q₁`-th
root of unity `z ∈ 𝓞 E`, divides `q₁` in `𝓞 E`. -/
lemma eval_derivative_cyclotomic_dvd_q₁ (hz : IsPrimitiveRoot z (P.q₁ s)) :
    (cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z ∣ P.q₁ s := by
  -- Differentiate `X ^ q₁ - 1 = f * Q` at the root `z` of `f` and multiply by `z`.
  set f : (𝓞 (P.E s))[X] := cyclotomic (P.q₁ s) (𝓞 (P.E s))
  have h_root : f.eval z = 0 := hz.isRoot_cyclotomic one_le
  obtain ⟨Q, hQ⟩ : f ∣ X ^ P.q₁ s - 1 := cyclotomic.dvd_X_pow_sub_one _ _
  refine ⟨Q.eval z * z, ?_⟩
  calc (P.q₁ s : 𝓞 (P.E s)) = (X ^ P.q₁ s - 1 : (𝓞 (P.E s))[X]).derivative.eval z * z := by
        simp [derivative_pow, mul_assoc, pow_sub_one_mul, hz.pow_eq_one, ne]
    _ = f.derivative.eval z * (Q.eval z * z) := by simp [hQ, h_root, mul_assoc]

/-- Let `z ∈ 𝓞 E` be a primitive `q₁`-th root of unity. The different of `ℚ(z)`, extended to `𝓞 E`,
is generated by the value at `z` of the derivative of the cyclotomic polynomial of level `q₁`.

This is the Euler–Dedekind formula for the different of a monogenic extension, in the case of the
cyclotomic field `ℚ(z)` over `ℚ`, stated after extension of the ideal to `𝓞 E`. -/
lemma map_differentIdeal_adjoin_eq_span (hz : IsPrimitiveRoot z (P.q₁ s)) :
    (differentIdeal ℤ (𝓞 ℚ⟮z.val⟯)).map (algebraMap (𝓞 ℚ⟮z.val⟯) (𝓞 (P.E s))) =
      span {(cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z} := by
  have hz_val : IsPrimitiveRoot z.val (P.q₁ s) := hz.map_of_injective coe_injective
  have : IsCyclotomicExtension {P.q₁ s} ℚ ℚ⟮z.val⟯ :=
    hz_val.intermediateField_adjoin_isCyclotomicExtension _
  have h_gen : IsPrimitiveRoot (AdjoinSimple.gen ℚ z.val) (P.q₁ s) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 hz_val
  -- The conductor of `ℤ[z]` times the different of `ℚ(z)` is generated by the derivative of the
  -- minimal polynomial at `z`; the ring of integers of `ℚ(z)` is `ℤ[z]`, so the conductor is `⊤`.
  set g : 𝓞 ℚ⟮z.val⟯ := h_gen.toInteger
  have h_cond : conductor ℤ g * differentIdeal ℤ (𝓞 ℚ⟮z.val⟯) =
      span {aeval g (minpoly ℤ g).derivative} :=
    conductor_mul_differentIdeal ℤ ℚ _ g (adjoin_primitive_root_eq_top h_gen)
  have h_minpoly : cyclotomic (P.q₁ s) ℤ = minpoly ℤ g :=
    (cyclotomic_eq_minpoly h_gen one_le).trans (minpoly_coe g)
  have h_image : algebraMap (𝓞 ℚ⟮z.val⟯) (𝓞 (P.E s)) g = z := rfl
  rw [conductor_eq_top_of_adjoin_eq_top (Rat.adjoin_singleton_eq_top h_gen), top_mul] at h_cond
  rw [h_cond, ← h_minpoly, map_span, Set.image_singleton, ← aeval_algebraMap_apply, h_image,
    ← eval_map_algebraMap, ← derivative_map, map_cyclotomic]

/-- Let `z ∈ 𝓞 E` be a primitive `q₁`-th root of unity, and `y` the value at `z` of the derivative
of the cyclotomic polynomial of level `q₁`. Then the ideal `(y)` divides the different of `E/K`. -/
lemma span_derivative_cyclotomic_dvd_differentIdeal (hz : IsPrimitiveRoot z (P.q₁ s)) :
    span {(cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z} ∣
      differentIdeal (𝓞 P.K) (𝓞 (P.E s)) := by
  -- `y` generates the different of `ℚ(z)` and is prime to `√-d`, which generates that of `K`.
  have h_coprime :
      IsCoprime (P.sqrtNegDInE s) ((cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z) :=
    (P.coprime_q₁_d s).symm.cast.mono sqrtNegDInE_dvd_d (eval_derivative_cyclotomic_dvd_q₁ hz)
  have h_coprime_different :
      IsCoprime ((differentIdeal ℤ (𝓞 P.K)).map (algebraMap (𝓞 P.K) (𝓞 (P.E s))))
        ((differentIdeal ℤ (𝓞 ℚ⟮z.val⟯)).map (algebraMap (𝓞 ℚ⟮z.val⟯) (𝓞 (P.E s)))) := by
    rwa [map_differentIdeal_eq_span_sqrtNegDInE, map_differentIdeal_adjoin_eq_span hz,
      isCoprime_span_singleton_iff]
  rw [← map_differentIdeal_adjoin_eq_span hz]
  exact IsDedekindDomain.map_differentIdeal_dvd_differentIdeal ℤ (𝓞 (P.E s)) (𝓞 P.K)
    (𝓞 ℚ⟮z.val⟯) h_coprime_different

/-- Let `z ∈ 𝓞 E` be a primitive `q₁`-th root of unity. The value at `z` of the derivative of the
cyclotomic polynomial of level `q₁` generates the different of `E/K`, and `𝓞 E = 𝓞 K[z]`. -/
lemma differentIdeal_eq_span_and_adjoin_eq_top (hz : IsPrimitiveRoot z (P.q₁ s)) :
    differentIdeal (𝓞 P.K) (𝓞 (P.E s)) =
      span {(cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z} ∧
    (𝓞 P.K)[z] = ⊤ := by
  have hz_val : IsPrimitiveRoot z.val (P.q₁ s) := hz.map_of_injective coe_injective
  have h_root : aeval z (cyclotomic (P.q₁ s) (𝓞 P.K)) = 0 := by
    rw [← eval_map_algebraMap, map_cyclotomic]
    exact hz.isRoot_cyclotomic one_le
  have h_deriv : aeval z (cyclotomic (P.q₁ s) (𝓞 P.K)).derivative =
      (cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z := by
    rw [← eval_map_algebraMap, ← derivative_map, map_cyclotomic]
  exact differentIdeal_eq_span_of_dvd P.K (adjoin_primitive_root_eq_top hz_val) _ h_root h_deriv
    (span_derivative_cyclotomic_dvd_differentIdeal hz)

/-- The different of `E/K` is generated by the derivative of the cyclotomic polynomial of level
`q₁` evaluated at a primitive `q₁`-th root of unity `z ∈ 𝓞 E`. -/
lemma differentIdeal_eq_span_derivative_cyclotomic (hz : IsPrimitiveRoot z (P.q₁ s)) :
    differentIdeal (𝓞 P.K) (𝓞 (P.E s)) =
      span {(cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z} :=
  (differentIdeal_eq_span_and_adjoin_eq_top hz).1

lemma adjoin_eq_top_of_isPrimitiveRoot (hz : IsPrimitiveRoot z (P.q₁ s)) : (𝓞 P.K)[z] = ⊤ :=
  (differentIdeal_eq_span_and_adjoin_eq_top hz).2

/-- The ring of integers of `E` is `ℤ[β_K, ζ]`, where `β_K = (1 + √-d) / 2` and `ζ` is the primitive
root of unity of order `q₁`. -/
lemma adjoin_betaKInE_zetaInt_eq_top : adjoin ℤ {P.betaKInE s, P.zetaInt s} = ⊤ := by
  -- `𝓞 K = ℤ[β_K]` and `𝓞 E = 𝓞 K[ζ]`
  have h_quad : adjoin ℤ {betaK P.d} = ⊤ := (different_eq_span_and_adjoin_betaK P.d).2
  simpa [adjoin_eq_top_of_isPrimitiveRoot isPrimitiveRoot_zetaInt, Set.pair_comm] using
    (adjoin_eq_adjoin_union ℤ {betaK P.d} {P.zetaInt s} h_quad).symm

/-! ### Summary for a primitive root of unity -/

/-- Let `z` be a primitive `q₁`-th root of unity in `𝓞 E`, and `y` the derivative at `z` of the
cyclotomic polynomial of level `q₁`. Then `y` divides `q₁`, `y` generates the different of `E/K`,
and `z` generates `𝓞 E` over `𝓞 K`. -/
lemma relDifferent_spec (hz : IsPrimitiveRoot z (P.q₁ s)) :
    (cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z ∣ P.q₁ s ∧
    span {(cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval z} =
      differentIdeal (𝓞 P.K) (𝓞 (P.E s)) ∧
    (𝓞 P.K)[z] = ⊤ :=
  ⟨eval_derivative_cyclotomic_dvd_q₁ hz, (differentIdeal_eq_span_derivative_cyclotomic hz).symm,
    adjoin_eq_top_of_isPrimitiveRoot hz⟩

/-! ### The generator P'(ζ) and the different of `E` -/

/-- The value at `ζ` of the derivative of the `q₁`-th cyclotomic polynomial, as an element of `𝓞 E`.
It generates the different of `E/K`. -/
abbrev relDifferentGen (P : Parameters) (s : ℕ) : 𝓞 (P.E s) :=
  (cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval (P.zetaInt s)

lemma relDifferentGen_dvd_q₁ : P.relDifferentGen s ∣ P.q₁ s :=
  eval_derivative_cyclotomic_dvd_q₁ isPrimitiveRoot_zetaInt

lemma differentIdeal_eq_span_relDifferentGen :
    differentIdeal (𝓞 P.K) (𝓞 (P.E s)) = span {P.relDifferentGen s} :=
  differentIdeal_eq_span_derivative_cyclotomic isPrimitiveRoot_zetaInt

@[simp↓]
lemma relDifferentGen_ne_zero (P : Parameters) (s : ℕ) : (relDifferentGen P s).val ≠ 0 :=
  coe_ne_zero_iff.2 (ne_zero_of_dvd_ne_zero (Nat.cast_ne_zero.2 (ne _)) relDifferentGen_dvd_q₁)

/-- The different of `E` over `ℚ` is generated by the product of the generator `relDifferentGen` of
the different of `E/K` and `√-d`. -/
lemma differentIdeal_eq_span_relDifferentGen_mul :
    differentIdeal ℤ (𝓞 (P.E s)) = span {P.relDifferentGen s * P.sqrtNegDInE s} := by
  -- transitivity of the different in `ℚ ⊆ K ⊆ E`
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 P.K),
    differentIdeal_eq_span_relDifferentGen, map_differentIdeal_eq_span_sqrtNegDInE,
    span_singleton_mul_span_singleton]

lemma conductor_mem_differentIdeal :
    ((P.q₁ s * P.d : ℕ) : 𝓞 (P.E s)) ∈ differentIdeal ℤ (𝓞 (P.E s)) := by
  rw [Nat.cast_mul, differentIdeal_eq_span_relDifferentGen_mul, mem_span_singleton]
  exact mul_dvd_mul relDifferentGen_dvd_q₁ sqrtNegDInE_dvd_d

/-! ### The imaginary generator -/

/-- The generator `relDifferentGen` of the different of `E/K` is the product of `ζ - a`, where
`ζ = zetaInt` is the chosen primitive `q₁`-th root of unity in `𝓞 E` and `a` runs over the other
primitive `q₁`-th roots of unity. -/
lemma relDifferentGen_eq_prod_sub [DecidableEq (𝓞 (P.E s))] :
    P.relDifferentGen s =
      ∏ a ∈ (primitiveRoots (P.q₁ s) (𝓞 (P.E s))).erase (P.zetaInt s), (P.zetaInt s - a) := by
  rw [relDifferentGen, cyclotomic_eq_prod_X_sub_primitiveRoots isPrimitiveRoot_zetaInt,
    ← mul_prod_erase _ _ ((mem_primitiveRoots (pos _)).2 isPrimitiveRoot_zetaInt)]
  simp [eval_prod]

/-- Let `ζ = P.zetaInt s` be the chosen primitive `q₁`-th root of unity in `𝓞 E`, `E = K(ζ)`. For
every primitive `q₁`-th root of unity `a` in `𝓞 E`, some `u` with `star u * u = 1` makes
`u * (ζ - a)` fixed by complex conjugation `star`. -/
lemma exists_unit_mul_zetaInt_sub_real {a : 𝓞 (P.E s)} (ha : IsPrimitiveRoot a (P.q₁ s)) :
    ∃ u : 𝓞 (P.E s), star u * u = 1 ∧ star (u * (P.zetaInt s - a)) = u * (P.zetaInt s - a) := by
  -- As `q₁` is even, `a = ζ ^ (2 * e + 1)`. With `i * i = -1`, take `u = i * star ζ ^ (e + 1)`:
  -- then `u * (ζ - a) = i * (star ζ ^ e - ζ ^ e)` is a product of two imaginary elements.
  obtain ⟨l, -, hl, rfl⟩ := isPrimitiveRoot_zetaInt.isPrimitiveRoot_iff.1 ha
  obtain ⟨e, rfl⟩ : Odd l :=
    (hl.of_dvd_right ((dvd_pow_self 2 s.succ_ne_zero).trans two_pow_dvd_q₁)).odd_of_right
  obtain ⟨i, hi_sq, hi_star⟩ : ∃ i : 𝓞 (P.E s), i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  set ξ : 𝓞 (P.E s) := P.zetaInt s
  have h_unit (n : ℕ) : star ξ ^ n * ξ ^ n = 1 := star_zetaInt_pow_mul_zetaInt_pow_eq_one n
  have h_factor : star ξ ^ (e + 1) * (ξ - ξ ^ (2 * e + 1)) = star ξ ^ e - ξ ^ e := by
    linear_combination star ξ ^ e * h_unit 1 - ξ ^ e * h_unit (e + 1)
  refine ⟨i * star ξ ^ (e + 1), ?_, ?_⟩
  · rw [star_mul', hi_star, star_pow, star_star]
    linear_combination -(star ξ ^ (e + 1) * ξ ^ (e + 1)) * hi_sq + h_unit (e + 1)
  · rw [mul_assoc, h_factor, star_mul', hi_star, star_sub, star_pow, star_pow, star_star]
    ring

/-- Some `c` in `𝓞 E` with `star c * c = 1` makes `c * relDifferentGen` fixed by complex
conjugation `star`; here `relDifferentGen` is the generator of the different of `E/K`. -/
lemma exists_unit_mul_relDifferentGen_real :
    ∃ c : 𝓞 (P.E s), star c * c = 1 ∧ star (c * P.relDifferentGen s) = c * P.relDifferentGen s := by
  classical
  -- `relDifferentGen` is the product of the `ζ - a`; multiply the units that make each factor real.
  set S : Finset (𝓞 (P.E s)) := (primitiveRoots (P.q₁ s) (𝓞 (P.E s))).erase (P.zetaInt s)
  have h_factor : ∀ a ∈ S, ∃ u : 𝓞 (P.E s), star u * u = 1 ∧
      star (u * (P.zetaInt s - a)) = u * (P.zetaInt s - a) := fun a ha ↦
    exists_unit_mul_zetaInt_sub_real (isPrimitiveRoot_of_mem_primitiveRoots (mem_of_mem_erase ha))
  choose! u hu hu_real using h_factor
  refine ⟨∏ a ∈ S, u a, ?_, ?_⟩
  · rw [star_prod, ← prod_mul_distrib, prod_eq_one hu]
  · rw [relDifferentGen_eq_prod_sub, ← prod_mul_distrib, star_prod, prod_congr rfl hu_real]

/-- A chosen `c` in `𝓞 E` with `star c * c = 1` such that `c * relDifferentGen` is fixed by
`star`; see `star_differentGenPhase_mul_self` and `star_differentGenPhase_mul_relDifferentGen`. -/
def differentGenPhase (P : Parameters) (s : ℕ) : 𝓞 (P.E s) :=
  (exists_unit_mul_relDifferentGen_real (P := P) (s := s)).choose

lemma star_differentGenPhase_mul_self : star (P.differentGenPhase s) * P.differentGenPhase s = 1 :=
  exists_unit_mul_relDifferentGen_real.choose_spec.1

/-- The product of `differentGenPhase` and the generator `relDifferentGen` of the different of `E/K`
is fixed by complex conjugation. -/
lemma star_differentGenPhase_mul_relDifferentGen :
    star (P.differentGenPhase s * P.relDifferentGen s) = P.differentGenPhase s * P.relDifferentGen
      s :=
  exists_unit_mul_relDifferentGen_real.choose_spec.2

lemma isUnit_differentGenPhase : IsUnit (P.differentGenPhase s) :=
  .of_mul_eq_one_right _ star_differentGenPhase_mul_self

/-- The element `c * relDifferentGen * √-d` of `𝓞 E`, where `c = differentGenPhase`; the comments
write `ϖ` for it. It is a purely imaginary generator of the different of `E`: see `star_deltaE` and
`differentIdeal_eq_span_deltaE`. -/
def deltaE (P : Parameters) (s : ℕ) : 𝓞 (P.E s) :=
  P.differentGenPhase s * (P.relDifferentGen s * P.sqrtNegDInE s)

lemma deltaE_def : P.deltaE s = P.differentGenPhase s * (P.relDifferentGen s * P.sqrtNegDInE s) :=
  rfl

/-- The generator `deltaE` of the different of `E` is purely imaginary: it is the product of a real
element and `√-d`. -/
lemma star_deltaE : star (P.deltaE s) = -P.deltaE s := by
  rw [deltaE_def, ← mul_assoc, star_mul', star_differentGenPhase_mul_relDifferentGen,
    star_sqrtNegDInE,
    mul_neg]

lemma differentIdeal_eq_span_deltaE : differentIdeal ℤ (𝓞 (P.E s)) = span {P.deltaE s} := by
  rw [deltaE_def, span_singleton_mul_left_unit isUnit_differentGenPhase,
    differentIdeal_eq_span_relDifferentGen_mul]

/-- The product of `v (P.deltaE s)` over all infinite places `v` of `E` (the type `P.Φ s`) is the
root discriminant of `E` raised to the number of infinite places. -/
lemma prod_deltaE_eq_rootDiscr_pow :
    ∏ v : P.Φ s, v (P.deltaE s).val = rootDiscr (P.E s) ^ Core.numInfPlaces (P.E s) := by
  -- The square of the product is `|N (P.deltaE s)|`, the norm of the different, that is
  -- `|discr E|`.
  have h_absNorm : absNorm (span {P.deltaE s}) = (discr (P.E s)).natAbs := by
    rw [← differentIdeal_eq_span_deltaE, absNorm_differentIdeal (P.E s)]
  rw [← sq_eq_sq₀ (prod_nonneg fun v _ ↦ apply_nonneg v _) (pow_pos (rootDiscr_pos _) _).le]
  calc (∏ v : P.Φ s, v (P.deltaE s).val) ^ 2 = |(norm ℚ (P.deltaE s).val : ℝ)| := by
        simpa [prod_pow] using prod_eq_abs_norm (P.deltaE s).val
    _ = |(discr (P.E s) : ℝ)| := by
        simpa [← coe_norm_int] using congrArg (Nat.cast : ℕ → ℝ) h_absNorm
    _ = (rootDiscr (P.E s) ^ Core.numInfPlaces (P.E s)) ^ 2 := by rw [abs_discr_eq_rootDiscr_pow]

/-- The element `c = differentGenPhase`, which satisfies `star c * c = 1`, has absolute value `1`
under the chosen embedding `Φ v : E →+* ℂ` at every infinite place `v`. -/
lemma norm_Φ_differentGenPhase (v : P.Φ s) : ‖Φ v (P.differentGenPhase s).val‖ = 1 := by
  have h_sq : ‖Φ v (P.differentGenPhase s).val‖ ^ 2 = 1 := by
    simpa [sq] using congrArg (fun x : 𝓞 (P.E s) ↦ ‖Φ v x.val‖) star_differentGenPhase_mul_self
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h_sq

/-- At every infinite place `v` of `E = P.E s`, `|deltaE|_v = |relDifferentGen|_v * √d`. Here
`deltaE` generates the different of `E/ℚ` and `relDifferentGen` the different of `E/K`. -/
lemma infinitePlace_apply_deltaE (v : P.Φ s) :
    v (P.deltaE s).val = v (P.relDifferentGen s).val * √P.d := by
  -- `deltaE = differentGenPhase * relDifferentGen * √-d`; read `v` through `Φ v : E →+* ℂ`
  have apply_eq_norm (x : P.E s) : v x = ‖Φ v x‖ := by rw [← apply, mk_Φ]
  have h_sqrt : ‖Φ v (P.sqrtNegDInE s).val‖ = √P.d := by simp
  simp only [apply_eq_norm, deltaE_def, map_mul, norm_mul, norm_Φ_differentGenPhase, h_sqrt,
    one_mul]

end Different

/-!
## Decomposition of rational primes in E

* `New.Parameters.intValuation_natCast_eq_exp_neg_one`: a prime not dividing `q₁ d` is unramified.
* `New.Parameters.smul_eq_self_iff_of_inert`, `New.Parameters.smul_eq_star_iff_of_inert`,
  `New.Parameters.q_eq_pow_lcm_of_inert`: the case `(p/d) = -1`, where `(p/d)` is `New.chiK d p`.
* `New.Parameters.natCast_dvd_pow_sub_galOfPlaceInt_star`: in that case, for odd `n`, the `pⁿ`-th
  power is modulo `p` complex conjugation followed by the Galois element named by `-pⁿ`.
-/

section Decomposition

open NumberField IsDedekindDomain HeightOneSpectrum Ideal Quotient FiniteField Algebra CharP ZMod
  NeZero QuadField Polynomial

attribute [local instance] Quotient.field ZMod.algebra

variable {P : Parameters} {s p : ℕ}

/-! ### The action on finite places and the Frobenius element -/

/-- The ring endomorphism of `𝓞 E` given by the element `σ_v = galOfPlace s v` of `Gal(E/K)`
attached to the infinite place `v`. -/
def galOfPlaceInt (v : P.Φ s) : 𝓞 (P.E s) →+* 𝓞 (P.E s) :=
  MulSemiringAction.toRingHom Gal(P.E s/P.K) (𝓞 (P.E s)) (P.galOfPlace s v)

@[simp]
theorem coe_galOfPlaceInt {v : P.Φ s} (x : 𝓞 (P.E s)) :
    (galOfPlaceInt v x : P.E s) = P.galOfPlace s v x := rfl

/-- An infinite place `v` acts on the finite places of `E` by pullback along the element
`galOfPlace s v` of `Gal(E/K)`. -/
instance : SMul (P.Φ s) (FinPlace (P.E s)) := ⟨(FinPlace.comap <| P.galOfPlace s ·)⟩

/-- An integer `x` of `E` lies in the prime `v • w` if and only if `σ_v x` lies in `w`, where `σ_v`
is the element of `Gal(E/K)` attached to `v`. -/
@[simp]
lemma mem_asIdeal_smul_iff {v : P.Φ s} {w : FinPlace (P.E s)} {x : 𝓞 (P.E s)} :
    x ∈ (v • w).asIdeal ↔ galOfPlaceInt v x ∈ w.asIdeal := .rfl

/-- The Frobenius element at the prime `p`: the pair of the place named by the integer `(p/d) p`
and the sign `(p/d) = chiK P.d p`. Let `p ∤ q₁ d` be prime and `e = ±1`. Then `(v, e)` is its
`n`-th power exactly when, modulo a prime above `p`, `galOfPlaceInt v` acts as the `n`-th power of
Frobenius, composed with complex conjugation if `e = -1`
(`New.Parameters.map_galOfPlaceInt_eq_pow_iff_eq_frobElem_pow`). -/
@[simp]
def frobElem (s p : ℕ) : P.Φ s × ℤ := (P.placeOfInt s (chiK P.d p * p), chiK P.d p)

/-- The pair `(c, e)` is the identity of `𝓞 E` with the sign `1`, or complex conjugation with the
sign `-1`. -/
def IsIdOrConjWithSign (c : 𝓞 (P.E s) ≃+* 𝓞 (P.E s)) (e : ℤ) : Prop :=
  c = RingEquiv.refl (𝓞 (P.E s)) ∧ e = 1 ∨ c = starRingAut ∧ e = -1

lemma isIdOrConjWithSign_refl : IsIdOrConjWithSign (RingEquiv.refl (𝓞 (P.E s))) 1 := .inl ⟨rfl, rfl⟩

lemma isIdOrConjWithSign_star : IsIdOrConjWithSign (starRingAut : 𝓞 (P.E s) ≃+* 𝓞 (P.E s)) (-1) :=
  .inr ⟨rfl, rfl⟩

lemma IsIdOrConjWithSign.sign_eq_one_or_neg_one {c : 𝓞 (P.E s) ≃+* 𝓞 (P.E s)} {e : ℤ}
    (h_sign : IsIdOrConjWithSign c e) : e = 1 ∨ e = -1 :=
  h_sign.imp And.right And.right

/-- Two ring maps `f g` from `𝓞 E` to a commutative ring `R` are equal if they agree at `zetaInt`
(the chosen primitive `q₁`-th root of unity `ζ`) and at `betaKInE = (1 + √-d) / 2`. -/
lemma ringHom_ext_zetaInt_betaKInE {R : Type*} [CommRing R] {f g : 𝓞 (P.E s) →+* R}
    (h_zeta : f (P.zetaInt s) = g (P.zetaInt s)) (h_beta : f (P.betaKInE s) = g (P.betaKInE s)) :
    f = g := by
  -- `𝓞 E = ℤ[betaKInE, zetaInt]`
  refine RingHom.toIntAlgHom_injective (AlgHom.ext_of_adjoin_eq_top adjoin_betaKInE_zetaInt_eq_top
    ?_)
  rintro x (rfl | rfl)
  exacts [h_beta, h_zeta]

lemma ne_two_of_not_dvd_q₁ (hp_not_dvd : ¬p ∣ P.q₁ s) : p ≠ 2 := by
  rintro rfl
  exact hp_not_dvd ((dvd_pow_self 2 s.succ_ne_zero).trans two_pow_dvd_q₁)

variable [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
  {v : P.Φ s} {w w' : FinPlace (P.E s)} {c : 𝓞 (P.E s) ≃+* 𝓞 (P.E s)} {e : ℤ}

lemma isCoprime_q₀_of_not_dvd (hp_not_dvd : ¬p ∣ P.q₁ s) : IsCoprime (p : ℤ) P.q₀ :=
  Nat.isCoprime_iff_coprime.2 <| hp.out.coprime_iff_not_dvd.2 fun h_dvd ↦
    hp_not_dvd (h_dvd.mul_right (towerDeg s))

/-- Let `E = P.E s`, `p ∤ q₁ = P.q₁ s` be prime, and `φ : 𝓞 E → R` a ring map to characteristic `p`.
Let `(c, e)` be the identity with sign `1` or complex conjugation with sign `-1`. Write
`σ v = galOfPlaceInt v` for the Galois element of the infinite place `v`. Then
`φ (σ v x) = φ (c x) ^ pⁿ` for all `x` exactly when two conditions on the generators hold. First,
`φ (σ v ζ) = φ (σ u ζ)` for `ζ = zetaInt`, with `u = placeOfInt (e pⁿ)` the place of the class of
`e pⁿ` in `(ℤ/q₁)ˣ`. Second, `(p/d)ⁿ e φ(√-d) = φ(√-d)`, with `√-d = P.sqrtNegDInE s`, `d = P.d` and
`(p/d) = chiK P.d p` the Legendre symbol. -/
lemma forall_map_galOfPlaceInt_eq_pow_iff (hp_not_dvd : ¬p ∣ P.q₁ s) (φ : 𝓞 (P.E s) →+* R) (n : ℕ)
    (h_sign : IsIdOrConjWithSign c e) :
    (∀ x : 𝓞 (P.E s), φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔
      φ (galOfPlaceInt v (P.zetaInt s)) =
          φ (galOfPlaceInt (P.placeOfInt s (e * p ^ n)) (P.zetaInt s)) ∧
        chiK P.d p ^ n * e * φ (P.sqrtNegDInE s) = φ (P.sqrtNegDInE s) := by
  -- Both sides of the equation are ring maps in `x`, and `𝓞 E = ℤ[betaKInE, zetaInt]`; so compare
  -- them at the two generators.
  have on_generators : (∀ x : 𝓞 (P.E s), φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔
      φ (galOfPlaceInt v (P.zetaInt s)) = φ (c (P.zetaInt s)) ^ p ^ n ∧
        φ (galOfPlaceInt v (P.betaKInE s)) = φ (c (P.betaKInE s)) ^ p ^ n := by
    refine ⟨fun h_all ↦ ⟨h_all _, h_all _⟩, fun ⟨h_zeta, h_beta⟩ ↦ ?_⟩
    exact DFunLike.congr_fun (ringHom_ext_zetaInt_betaKInE (f := φ.comp (galOfPlaceInt v))
      (g := (iterateFrobenius R p n).comp (φ.comp c.toRingHom)) h_zeta h_beta)
  -- At `zetaInt`: conjugation inverts it, so both sides are `ζ ^ (e * p ^ n)`.
  have at_zeta : c (P.zetaInt s) ^ p ^ n =
      galOfPlaceInt (P.placeOfInt s (e * p ^ n)) (P.zetaInt s) := by
    have h_coprime : IsCoprime ((p : ℤ) ^ n) P.q₀ := (isCoprime_q₀_of_not_dvd hp_not_dvd).pow_left
    rcases h_sign with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [RingOfIntegers.ext_iff, ← zpow_natCast,
      galOfPlace_placeOfInt_zeta h_coprime, galOfPlace_placeOfInt_zeta h_coprime.neg_left]
  -- At `betaKInE`: Frobenius multiplies `√-d = 2 * betaKInE - 1` by `chiK P.d p`.
  have at_beta : φ (galOfPlaceInt v (P.betaKInE s)) = φ (c (P.betaKInE s)) ^ p ^ n ↔
      2 * φ (galOfPlaceInt v (P.betaKInE s)) - 1 = chiK P.d p ^ n * φ (c (P.sqrtNegDInE s)) :=
    eq_map_betaK_pow_iff (ne_two_of_not_dvd_q₁ hp_not_dvd)
      (φ.comp (c.toRingHom.comp (algebraMap (𝓞 P.K) (𝓞 (P.E s))))) n _
  -- `galOfPlaceInt v` fixes `betaKInE`, and `c` multiplies `√-d` by `e`.
  have gal_beta : 2 * φ (galOfPlaceInt v (P.betaKInE s)) - 1 = φ (P.sqrtNegDInE s) := by
    simp [galOfPlaceInt, sqrtNegDInE, map_ofNat]
  have c_sqrt : c (P.sqrtNegDInE s) = e * P.sqrtNegDInE s := by
    rcases h_sign with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [star_sqrtNegDInE]
  rw [on_generators, ← map_pow, at_zeta, at_beta, gal_beta, c_sqrt, map_mul, map_intCast, mul_assoc,
    eq_comm (a := φ (P.sqrtNegDInE s))]

/-- For a prime `p ∤ d`, every power of the Legendre symbol `(p/d)` is `1` or `-1`. -/
lemma chiK_pow_eq_one_or_neg_one (hp_not_dvd : ¬p ∣ P.d) (n : ℕ) :
    chiK P.d p ^ n = 1 ∨ chiK P.d p ^ n = -1 := by
  rcases chiK_cases P.d p with ⟨h_eq, -⟩ | ⟨-, h_chi | h_chi⟩
  · exact absurd h_eq.dvd hp_not_dvd
  · simp [h_chi]
  · simpa [h_chi] using neg_one_pow_eq_or ℤ n

omit [Fact p.Prime] in
/-- Let `φ : 𝓞 E → R` be a ring map to a domain whose characteristic `p` does not divide `q₁`.
For infinite places `u v : P.Φ s`, write `σ v = galOfPlaceInt v` for the Galois element of `E/K`
attached to `v`, a ring endomorphism of `𝓞 E`. Let `ζ = zetaInt` be the chosen primitive `q₁`-th
root of unity in `𝓞 E`. Then `φ (σ v ζ) = φ (σ u ζ)` if and only if `v = u`. -/
lemma map_galOfPlaceInt_zetaInt_inj [IsDomain R] (φ : 𝓞 (P.E s) →+* R) (hp_not_dvd : ¬p ∣ P.q₁ s)
    (u : P.Φ s) :
    φ (galOfPlaceInt v (P.zetaInt s)) = φ (galOfPlaceInt u (P.zetaInt s)) ↔ v = u := by
  -- `φ zetaInt` is still a primitive `q₁`-th root of unity
  have : NeZero (P.q₁ s : R) := of_not_dvd R hp_not_dvd
  have primitive : IsPrimitiveRoot (φ (P.zetaInt s)) (P.q₁ s) := isRoot_cyclotomic_iff.1 <| by
    simpa using (isPrimitiveRoot_zetaInt.isRoot_cyclotomic one_le).map (f := φ)
  -- `σ_t` raises `ζ` to the residue modulo `q₁` that names `t`
  let residue (t : P.Φ s) : ZMod (P.q₁ s) := P.placeMulEquiv s t
  have gal_zeta (t : P.Φ s) : galOfPlaceInt t (P.zetaInt s) = P.zetaInt s ^ (residue t).val :=
    RingOfIntegers.ext (galOfPlace_zeta t)
  rw [gal_zeta, gal_zeta, map_pow, map_pow]
  refine ⟨fun h_eq ↦ ?_, fun h_eq ↦ by rw [h_eq]⟩
  simpa [residue, Units.val_inj] using
    val_injective _ (primitive.pow_inj (val_lt _) (val_lt _) h_eq)

/-- Let `p ∤ q₁ d` be prime, `φ : 𝓞 E → R` a ring map to a domain of characteristic `p`, and `c`
the identity or complex conjugation, with sign `e`. Write `σ v = galOfPlaceInt v` for the Galois
element of the infinite place `v`. Then `φ (σ v x) = φ (c x) ^ pⁿ` for all `x` exactly when
`(v, e)` is the `n`-th power of the Frobenius element at `p`, the pair of the place of the class of
`(p/d) p` in `(ℤ/q₁)ˣ` and the Legendre symbol `(p/d)`. -/
lemma map_galOfPlaceInt_eq_pow_iff_eq_frobElem_pow [IsDomain R] (φ : 𝓞 (P.E s) →+* R) (n : ℕ)
    (h_sign : IsIdOrConjWithSign c e) (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    (∀ x : 𝓞 (P.E s), φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔
      (v, e) = P.frobElem s p ^ n := by
  -- The first condition of `forall_map_galOfPlaceInt_eq_pow_iff` determines `v`; as
  -- `φ sqrtNegDInE ≠ 0`, the second one determines `e`.
  obtain ⟨hp_not_dvd_q₁, hp_not_dvd_d⟩ : ¬p ∣ P.q₁ s ∧ ¬p ∣ P.d := by
    rwa [hp.out.dvd_mul, not_or] at hp_not_dvd
  have sqrt_sq : φ (P.sqrtNegDInE s) ^ 2 = -P.d :=
    map_sqrtNegDInt_sq (φ.comp (algebraMap (𝓞 P.K) (𝓞 (P.E s))))
  have sqrt_ne_zero : φ (P.sqrtNegDInE s) ≠ 0 := fun h_zero ↦ by
    simp [h_zero, CharP.cast_eq_zero_iff R p, hp_not_dvd_d] at sqrt_sq
  -- `chiK P.d p ^ n` and `e` are `1` or `-1`, which stay distinct in `R` because `p ≠ 2`
  have neg_one_ne_one : (-1 : R) ≠ 1 := by
    simpa [_root_.neg_one_eq_one_iff, ringChar.eq R p] using ne_two_of_not_dvd_q₁ hp_not_dvd_q₁
  have sign_iff : chiK P.d p ^ n * e * φ (P.sqrtNegDInE s) = φ (P.sqrtNegDInE s) ↔
      e = chiK P.d p ^ n := by
    rw [mul_left_eq_self₀, or_iff_left sqrt_ne_zero, ← Int.cast_pow]
    rcases chiK_pow_eq_one_or_neg_one hp_not_dvd_d n with h_pow | h_pow <;>
      rcases h_sign.sign_eq_one_or_neg_one with rfl | rfl <;> simp [h_pow, neg_one_ne_one]
  have frobElem_pow : P.frobElem s p ^ n =
      (P.placeOfInt s (chiK P.d p ^ n * p ^ n), chiK P.d p ^ n) := by simp [placeOfInt_pow, mul_pow]
  rw [forall_map_galOfPlaceInt_eq_pow_iff hp_not_dvd_q₁ φ n h_sign,
    map_galOfPlaceInt_zetaInt_inj φ hp_not_dvd_q₁, sign_iff, frobElem_pow, Prod.mk.injEq]
  exact and_congr_left fun he : e = chiK P.d p ^ n ↦ by rw [he]

/-! ### Decomposition groups, norms and ramification -/

/-- Let `v : P.Φ s` be an infinite place of `E`, and write `σ v = galOfPlaceInt v` for its Galois
element of `E/K`, a ring endomorphism of `𝓞 E`. Let `w` be a place above the prime `p`, and let `c`
be any ring automorphism of `𝓞 E`. If `v • w` is also the pullback of `w` along `c`, then for some
`n : ℕ`, `σ v x ≡ (c x) ^ (p ^ n)` modulo `w` for all `x ∈ 𝓞 E`. -/
lemma exists_mk_galOfPlaceInt_eq_pow_of_smul_eq (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (h_smul : v • w = HeightOneSpectrum.comap c c.surjective w) :
    ∃ n : ℕ, ∀ x : 𝓞 (P.E s), Ideal.Quotient.mk w.asIdeal (galOfPlaceInt v x) =
      Ideal.Quotient.mk w.asIdeal (c x) ^ p ^ n := by
  -- `galOfPlaceInt v ∘ c⁻¹` induces an endomorphism of the residue field, a power of Frobenius.
  have : CharP (𝓞 (P.E s) ⧸ w.asIdeal) p := w.charP_quotient hp_mem
  have h_mem (x : 𝓞 (P.E s)) : galOfPlaceInt v x ∈ w.asIdeal ↔ c x ∈ w.asIdeal := by
    rw [← mem_asIdeal_smul_iff, h_smul]
    rfl
  have le_comap : w.asIdeal ≤ w.asIdeal.comap ((galOfPlaceInt v).comp c.symm) :=
    fun x hx ↦ (h_mem (c.symm x)).2 (by simpa using hx)
  let induced : (𝓞 (P.E s) ⧸ w.asIdeal) →ₐ[ZMod p] 𝓞 (P.E s) ⧸ w.asIdeal :=
    .mk' (quotientMap _ _ le_comap) (ZMod.map_smul _)
  obtain ⟨⟨n, -⟩, hn : frobeniusAlgHom (ZMod p) (𝓞 (P.E s) ⧸ w.asIdeal) ^ n = induced⟩ :=
    (bijective_frobeniusAlgHom_pow (ZMod p) _).surjective induced
  exact ⟨n, fun x ↦ by simpa [induced, coe_frobeniusAlgHom] using
    (DFunLike.congr_fun hn (Ideal.Quotient.mk w.asIdeal (c x))).symm⟩

/-- The decomposition group is generated by the Frobenius element. Let `p ∤ q₁ d` be prime, `w` a
finite place of `E = K(ζ)` above `p`, and `c` the identity (sign `e = 1`) or complex conjugation
(sign `e = -1`). The Frobenius element `P.frobElem s p` is the pair of the place of the class of
`(p/d) p` in `(ℤ/q₁)ˣ` and the Legendre symbol `(p/d) = chiK P.d p`. Then `v • w`, the pullback of
`w` along the Galois element of the infinite place `v`, is the pullback of `w` along `c` exactly
when `(v, e)` is a power of this pair. -/
lemma smul_eq_iff_exists_frobElem_pow (h_sign : IsIdOrConjWithSign c e)
    (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    v • w = HeightOneSpectrum.comap c c.surjective w ↔ ∃ n : ℕ, (v, e) = P.frobElem s p ^ n := by
  have : CharP (𝓞 (P.E s) ⧸ w.asIdeal) p := w.charP_quotient hp_mem
  let π : 𝓞 (P.E s) →+* 𝓞 (P.E s) ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
  have frob_iff (n : ℕ) : (v, e) = P.frobElem s p ^ n ↔
      ∀ x : 𝓞 (P.E s), π (galOfPlaceInt v x) = π (c x) ^ p ^ n :=
    (map_galOfPlaceInt_eq_pow_iff_eq_frobElem_pow π n h_sign hp_not_dvd).symm
  simp only [frob_iff]
  refine ⟨exists_mk_galOfPlaceInt_eq_pow_of_smul_eq hp_mem, fun ⟨n, h_frob⟩ ↦ ?_⟩
  -- modulo `w`, `galOfPlaceInt v x` is a power of `c x`, so the two vanish together
  ext x
  change galOfPlaceInt v x ∈ w.asIdeal ↔ c x ∈ w.asIdeal
  rw [← eq_zero_iff_mem, ← eq_zero_iff_mem, h_frob, pow_eq_zero_iff (pow_ne_zero n hp.out.ne_zero)]

/-- Let `p ∤ q₁ d` be prime and `w` a place above `p`. Then `v`, read in `Gal(E/K) = (ℤ/q₁)ˣ`, fixes
`w` exactly when `(v, 1)` is a power of the Frobenius element `((p/d) p, (p/d))` at `p`. -/
lemma smul_eq_self_iff_exists_frobElem_pow (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    v • w = w ↔ ∃ n : ℕ, (v, (1 : ℤ)) = P.frobElem s p ^ n :=
  smul_eq_iff_exists_frobElem_pow isIdOrConjWithSign_refl hp_mem hp_not_dvd

/-- Let `p ∤ q₁ d` be prime and `w` a place above `p`. Then `v`, read in `Gal(E/K) = (ℤ/q₁)ˣ`, sends
`w` to `w̄` exactly when `(v, -1)` is a power of the Frobenius element `((p/d) p, (p/d))` at `p`. -/
lemma smul_eq_star_iff_exists_frobElem_pow (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    v • w = star w ↔ ∃ n : ℕ, (v, (-1 : ℤ)) = P.frobElem s p ^ n :=
  smul_eq_iff_exists_frobElem_pow isIdOrConjWithSign_star hp_mem hp_not_dvd

/-- Let `p ∤ q₁ d` be prime and `w` a place of `E` above `p`. Then the norm `w.q` of `w` is `p ^ m`,
where `m` is the order of the Frobenius element `frobElem s p` at `p`. -/
lemma q_eq_pow_orderOf_frobElem (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    w.q = p ^ orderOf (P.frobElem s p) := by
  -- The order and the residue degree `f` have the same multiples `n`: those with
  -- `x ^ p ^ n ≡ x` modulo `w` for all `x`.
  have : CharP (𝓞 (P.E s) ⧸ w.asIdeal) p := w.charP_quotient hp_mem
  let π : 𝓞 (P.E s) →+* 𝓞 (P.E s) ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
  obtain ⟨f, hq, hf⟩ : ∃ f, w.q = p ^ f ∧ ∀ n : ℕ, f ∣ n ↔ ∀ x : 𝓞 (P.E s), π x ^ p ^ n = π x :=
    w.exists_q_eq_pow hp_mem
  have frob_iff (n : ℕ) : (∀ x : 𝓞 (P.E s), π x ^ p ^ n = π x) ↔ P.frobElem s p ^ n = 1 := by
    simpa [galOfPlaceInt, eq_comm, Prod.ext_iff] using
      map_galOfPlaceInt_eq_pow_iff_eq_frobElem_pow (v := 1) π n isIdOrConjWithSign_refl hp_not_dvd
  have order_eq : orderOf (P.frobElem s p) = f :=
    Nat.dvd_right_iff_eq.1 fun n ↦ by rw [orderOf_dvd_iff_pow_eq_one, hf, frob_iff]
  rw [hq, order_eq]

/-- Let `p ∤ q₁ d` be prime and `w` a place above `p`. Then `p` does not lie in the square of the
prime ideal `w`. -/
lemma natCast_notMem_sq (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    (p : 𝓞 (P.E s)) ∉ w.asIdeal ^ 2 := by
  -- otherwise `w ^ 2 ∋ p` makes `w` divide the different, which contains `q₁ * d`
  refine fun h_sq ↦ hp_not_dvd ((w.natCast_mem_iff_dvd hp_mem).1 ?_)
  exact le_of_dvd (dvd_differentIdeal_of_mem_sq h_sq) conductor_mem_differentIdeal

/-- Let `p ∤ q₁ d` be prime and `w` a finite place of `E` above `p`. Then `p` has order exactly `1`
at `w` (multiplicative valuation `exp (-1)`); so `p` is unramified at `w`. -/
lemma intValuation_natCast_eq_exp_neg_one (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (hp_not_dvd : ¬p ∣ P.q₁ s * P.d) :
    w.intValuation p = WithZero.exp (-1) := by
  have mult : multiplicity w.asIdeal (span {(p : 𝓞 (P.E s))}) = 1 :=
    multiplicity_eq_of_dvd_of_not_dvd (by simpa using hp_mem)
      (by simpa using natCast_notMem_sq hp_mem hp_not_dvd)
  simp [intValuation_eq_exp_neg_multiplicity, ne, mult]

open scoped Pointwise in
/-- The group `Gal(E/ℚ)` acts transitively on the finite places of `E` above a prime `p`. -/
lemma exists_gal_smul_mem_iff (hw : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (hw' : (p : 𝓞 (P.E s)) ∈ w'.asIdeal) :
    ∃ σ : Gal(P.E s/ℚ), ∀ x : 𝓞 (P.E s), σ • x ∈ w.asIdeal ↔ x ∈ w'.asIdeal := by
  have under_eq : w'.asIdeal.under ℤ = w.asIdeal.under ℤ := by
    ext n
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;>
      simp [w.natCast_mem_iff_dvd hw, w'.natCast_mem_iff_dvd hw']
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(P.E s/ℚ), w.asIdeal = σ • w'.asIdeal :=
    IsInvariant.exists_smul_of_under_eq ℤ _ Gal(P.E s/ℚ) w'.asIdeal w.asIdeal under_eq
  exact ⟨σ, fun x ↦ by simp [hσ]⟩

/-- Let `w` and `w'` be finite places of `E` above the prime `p`. Then `w'` is `v • w` or its
conjugate for some infinite place `v`, read as an element of `Gal(E/K)`. -/
lemma exists_smul_eq_or_star (hw : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (hw' : (p : 𝓞 (P.E s)) ∈ w'.asIdeal) :
    ∃ v : P.Φ s, v • w = w' ∨ star (v • w) = w' := by
  -- Some `σ` in `Gal(E/ℚ)` moves `w'` to `w`. The chosen embedding `Φ u : E →+* ℂ` at a place `u`
  -- is `Φ 1 ∘ galOfPlace u` (`phi_mul`). For the place `v` of `φ = Φ 1 ∘ σ`, `Φ v` is `φ` or its
  -- conjugate (`Φ_mk_eq_or_star_eq`), so `galOfPlace v` is `σ` or `σ` composed with conjugation.
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(P.E s/ℚ), ∀ x : 𝓞 (P.E s), σ • x ∈ w.asIdeal ↔ x ∈ w'.asIdeal :=
    exists_gal_smul_mem_iff hw hw'
  let φ : P.E s →+* ℂ := (Φ 1).comp σ.toRingHom
  let v : P.Φ s := .mk φ
  have φ_apply (x : 𝓞 (P.E s)) : φ x = Φ 1 ((σ • x : 𝓞 (P.E s)) : P.E s) := rfl
  have Φ_apply (x : 𝓞 (P.E s)) : Φ v (x : P.E s) = Φ 1 (galOfPlaceInt v x : P.E s) := by
    rw [coe_galOfPlaceInt, ← phi_mul, one_mul]
  refine ⟨v, (Φ_mk_eq_or_star_eq φ).imp (fun hφ : Φ v = φ ↦ ?_) (fun hφ : star (Φ v) = φ ↦ ?_)⟩
  · have gal_eq (x : 𝓞 (P.E s)) : galOfPlaceInt v x = σ • x :=
      RingOfIntegers.ext ((Φ 1).injective (by rw [← Φ_apply, ← φ_apply, hφ]))
    ext x
    rw [mem_asIdeal_smul_iff, gal_eq, hσ]
  · have gal_eq (x : 𝓞 (P.E s)) : galOfPlaceInt v (star x) = σ • x := by
      refine RingOfIntegers.ext ((Φ 1).injective ?_)
      rw [← Φ_apply, ← φ_apply, ← hφ]
      simp
    ext x
    rw [mem_star_place, mem_asIdeal_smul_iff, gal_eq, hσ]

/-! ### Inert primes and self-conjugate places -/

/-- A prime `p` with Legendre symbol `(p/d) = -1` does not divide `q₁ d`. -/
@[local simp]
lemma not_dvd_q₁_mul_d_of_inert (h_inert : chiK P.d p = -1) : ¬p ∣ P.q₁ s * P.d := by
  -- primes that divide `q₁` have character `1`, and `d` has character `0`
  refine hp.out.not_dvd_mul (fun hp_dvd_q₁ ↦ ?_) (fun hp_dvd_d ↦ ?_)
  · simp [P.chiK_eq_one_of_dvd hp.out hp_dvd_q₁] at h_inert
  · obtain rfl : p = P.d := (Nat.prime_dvd_prime_iff_eq hp.out P.d_prime).1 hp_dvd_d
    simp [natCast_self, MulChar.map_zero] at h_inert

/-- Let `p` be a prime with Legendre symbol `(p/d) = -1` and `w` a place of `E` above `p`. An
infinite place `v`, read as an element of `Gal(E/K)`, fixes `w` if and only if `v` is an even power
of the place named by `-p`. -/
lemma smul_eq_self_iff_of_inert (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (h_inert : chiK P.d p = -1) :
    v • w = w ↔ ∃ n : ℕ, v = P.placeOfInt s (-p) ^ n ∧ Even n := by
  -- the Frobenius element is `(-p, -1)`, and `(-1) ^ n = 1` says that `n` is even
  rw [smul_eq_self_iff_exists_frobElem_pow hp_mem (not_dvd_q₁_mul_d_of_inert h_inert)]
  simp [h_inert, neg_one_pow_eq_ite]

/-- Let `p` be a prime with Legendre symbol `(p/d) = -1` and `w` a place of `E` above `p`. An
infinite place `v`, read as an element of `Gal(E/K)`, sends `w` to its conjugate `star w` if and
only if `v` is an odd power of the place named by `-p`. -/
lemma smul_eq_star_iff_of_inert (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (h_inert : chiK P.d p = -1) :
    v • w = star w ↔ ∃ n : ℕ, v = P.placeOfInt s (-p) ^ n ∧ Odd n := by
  -- the Frobenius element is `(-p, -1)`, and `(-1) ^ n = -1` says that `n` is odd
  rw [smul_eq_star_iff_exists_frobElem_pow hp_mem (not_dvd_q₁_mul_d_of_inert h_inert)]
  simp [h_inert, neg_one_pow_eq_ite]

/-- Let `p` be a prime inert in `K`, that is `(p/d) = chiK P.d p = -1`, let `n` be odd, and let `τ`
be the element of `Gal(E/K)` at the place `P.placeOfInt s (-p ^ n)` of the class of `-pⁿ` in
`(ℤ/q₁)ˣ`. Then `y ^ pⁿ ≡ τ ȳ` modulo `p` for every integer `y` of `E`. -/
lemma natCast_dvd_pow_sub_galOfPlaceInt_star (hp_inert : chiK P.d p = -1) {n : ℕ} (hn : Odd n)
    (y : 𝓞 (P.E s)) :
    (p : 𝓞 (P.E s)) ∣ y ^ p ^ n - galOfPlaceInt (P.placeOfInt s (-p ^ n)) (star y) := by
  -- Modulo `p`, the `n`-th power of Frobenius is `τ` composed with conjugation
  -- (`forall_map_galOfPlaceInt_eq_pow_iff`).
  obtain ⟨w, hp_mem⟩ : ∃ w : FinPlace (P.E s), (p : 𝓞 (P.E s)) ∈ w.asIdeal :=
    FinPlace.exists_natCast_mem (P.E s) p
  let Q : Type := 𝓞 (P.E s) ⧸ Ideal.span {(p : 𝓞 (P.E s))}
  have : CharP Q p := CharP.quotient _ p (coe_subset_nonunits w.isPrime.ne_top hp_mem)
  let π : 𝓞 (P.E s) →+* Q := Ideal.Quotient.mk _
  have hp_not_dvd_q₁ : ¬p ∣ P.q₁ s :=
    fun h_dvd ↦ not_dvd_q₁_mul_d_of_inert hp_inert (h_dvd.mul_right P.d)
  have h_sign : (chiK P.d p : Q) ^ n * (-1 : ℤ) = 1 := by
    rw [hp_inert, Int.cast_neg, Int.cast_one, hn.neg_one_pow, neg_mul_neg, mul_one]
  have h_frob : π (galOfPlaceInt (P.placeOfInt s (-p ^ n)) (star y)) =
      π (starRingAut (star y)) ^ p ^ n :=
    (forall_map_galOfPlaceInt_eq_pow_iff hp_not_dvd_q₁ π n isIdOrConjWithSign_star).2
      ⟨by rw [neg_one_mul], by rw [h_sign, one_mul]⟩ (star y)
  rw [starRingAut_apply, star_star, ← map_pow] at h_frob
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h_frob.symm)

/-- A finite place of `E` that is its own complex conjugate does not contain `β_K β̄_K`, where
`β_K = betaKInE = (1 + √-d) / 2`. -/
lemma betaKInE_mul_star_notMem_of_star_eq (h_star : star w = w) :
    P.betaKInE s * star (P.betaKInE s) ∉ w.asIdeal := by
  -- otherwise `w` contains both factors, and their sum is `1`
  intro h_norm
  have h_iff : star (P.betaKInE s) ∈ w.asIdeal ↔ P.betaKInE s ∈ w.asIdeal := by
    rw [← mem_star_place, h_star]
  have h_mem : P.betaKInE s ∈ w.asIdeal := by simpa [h_iff] using w.isPrime.mem_or_mem h_norm
  exact w.isPrime.one_notMem (by simpa [star_betaKInE] using add_mem (h_iff.2 h_mem) h_mem)

/-- A prime `p` below a finite place of `E` that is its own complex conjugate does not divide
`q₁`. -/
lemma not_dvd_q₁_of_star_eq (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (h_star : star w = w) :
    ¬p ∣ P.q₁ s := by
  -- a prime that divides `q₁` divides `(d + 1) / 4 = betaKInE * star betaKInE`
  refine fun h_dvd ↦ betaKInE_mul_star_notMem_of_star_eq h_star ?_
  rw [star_betaKInE, betaKInE_mul_one_sub, w.natCast_mem_iff_dvd hp_mem]
  exact P.dvd_d_add_one_div_four_of_dvd_q₁ hp.out h_dvd

/-- Let `w` be a finite place of `E = P.E s` above the prime `p`, i.e. `p ∈ w.asIdeal`. If `w`
equals its complex conjugate `star w`, then `p ≡ -1` modulo `2 ^ (s + 1)`. -/
lemma natCast_eq_neg_one_of_star_eq (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (h_star : star w = w) :
    (p : ZMod (2 ^ (s + 1))) = -1 := by
  have : CharP (𝓞 (P.E s) ⧸ w.asIdeal) p := w.charP_quotient hp_mem
  have h_one : (1 : P.Φ s) • w = star w := by
    simp [HeightOneSpectrum.ext_iff, Ideal.ext_iff, h_star, galOfPlaceInt]
  have hp_not_dvd_q₁ : ¬p ∣ P.q₁ s := not_dvd_q₁_of_star_eq hp_mem h_star
  rcases chiK_cases P.d p with ⟨rfl, -⟩ | ⟨hp_ne_d, h_split | h_inert⟩
  · -- For `p = d` conjugation is a power of Frobenius on `ζ`, so some `-d ^ n` is `1` modulo `q₀`.
    let π : 𝓞 (P.E s) →+* 𝓞 (P.E s) ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
    obtain ⟨n, h_frob⟩ :
        ∃ n : ℕ, ∀ x : 𝓞 (P.E s), π (galOfPlaceInt 1 x) = π (starRingAut x) ^ P.d ^ n :=
      exists_mk_galOfPlaceInt_eq_pow_of_smul_eq hp_mem h_one
    have h_zeta : π (galOfPlaceInt 1 (P.zetaInt s)) =
        π (galOfPlaceInt (P.placeOfInt s (-1 * P.d ^ n)) (P.zetaInt s)) :=
      ((forall_map_galOfPlaceInt_eq_pow_iff hp_not_dvd_q₁ π n isIdOrConjWithSign_star).1
        h_frob).1
    have h_place : 1 = P.placeOfInt s (-P.d ^ n) := by
      simpa using (map_galOfPlaceInt_zetaInt_inj π hp_not_dvd_q₁ _).1 h_zeta
    have h_class : ((-P.d ^ n : ℤ) : ZMod P.q₀) = 1 := by
      rw [← placeClass_placeOfInt (isCoprime_q₀_of_not_dvd hp_not_dvd_q₁).pow_left.neg_left
        (h_dvd := P.q₀.dvd_mul_right (towerDeg s)), ← h_place, map_one, Units.val_one]
    have h_pow : (P.d : ZMod P.q₀) ^ n = -1 := by simpa [neg_eq_iff_eq_neg] using h_class
    exact absurd h_pow (P.d_pow_ne_neg_one n)
  · -- For split `p` the Frobenius element has sign `1`.
    have h_not_dvd : ¬p ∣ P.q₁ s * P.d :=
      hp.out.not_dvd_mul hp_not_dvd_q₁ (by rwa [Nat.prime_dvd_prime_iff_eq hp.out P.d_prime])
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ((1 : P.Φ s), (-1 : ℤ)) = P.frobElem s p ^ n :=
      (smul_eq_star_iff_exists_frobElem_pow hp_mem h_not_dvd).1 h_one
    have h_sign : (-1 : ℤ) = chiK P.d p ^ n := congrArg Prod.snd hn
    simp [h_split] at h_sign
  · -- For inert `p` an odd power of `-p` is `1`, and `(ℤ / 2 ^ (s + 1))ˣ` has order `2 ^ s`.
    obtain ⟨n, hn, h_odd⟩ : ∃ n : ℕ, 1 = P.placeOfInt s (-p) ^ n ∧ Odd n :=
      (smul_eq_star_iff_of_inert hp_mem h_inert).1 h_one
    set u : (ZMod (2 ^ (s + 1)))ˣ := P.placeClass two_pow_dvd_q₁ (P.placeOfInt s (-p)) with hu
    have h_pow : u ^ n = 1 := by rw [hu, ← map_pow, ← hn, map_one]
    have h_card : u ^ 2 ^ s = 1 := by
      simpa [Nat.totient_prime_pow_succ Nat.prime_two] using ZMod.pow_totient u
    have h_unit : u = 1 :=
      (pow_eq_one_iff_of_coprime (h_odd.coprime_two_right.pow_right s)).1 ⟨h_pow, h_card⟩
    have h_val : (u : ZMod (2 ^ (s + 1))) = (-p : ℤ) :=
      placeClass_placeOfInt (isCoprime_q₀_of_not_dvd hp_not_dvd_q₁).neg_left
    simpa [h_unit, eq_neg_iff_add_eq_zero, add_comm] using h_val

/-- Let `p` be a prime with Legendre symbol `(p/d) = -1` and `w` a place of `E` above `p`. Then the
norm `w.q` of `w` is `p ^ lcm o 2`, where `o` is the order of the infinite place named by `-p`, that
is of the class of `-p` in `(ℤ/q₁)ˣ`. -/
lemma q_eq_pow_lcm_of_inert (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) (h_inert : chiK P.d p = -1) :
    w.q = p ^ (orderOf (P.placeOfInt s (-p))).lcm 2 := by
  rw [q_eq_pow_orderOf_frobElem hp_mem (not_dvd_q₁_mul_d_of_inert h_inert), Prod.orderOf]
  simp [h_inert]

/-! ### Primes congruent to `1` modulo `q₁ d` -/

omit [Fact p.Prime] in
lemma chiK_eq_one_of_modEq_one (hp_modEq : p ≡ 1 [MOD P.q₁ s * P.d]) : chiK P.d p = 1 := by
  simp [(natCast_eq_natCast_iff p 1 P.d).2 hp_modEq.of_mul_left]

/-- A prime `p ≡ 1` modulo `q₁ d` does not divide `q₁ d`. -/
@[local simp]
lemma not_dvd_q₁_mul_d_of_modEq_one (hp_modEq : p ≡ 1 [MOD P.q₁ s * P.d]) :
    ¬p ∣ P.q₁ s * P.d := fun h_dvd ↦ hp.out.not_dvd_one ((hp_modEq.dvd_iff h_dvd).1 dvd_rfl)

omit [Fact p.Prime] in
lemma frobElem_eq_one (hp_modEq : p ≡ 1 [MOD P.q₁ s * P.d]) : P.frobElem s p = 1 := by
  simp [placeOfInt, chiK_eq_one_of_modEq_one hp_modEq,
    (natCast_eq_natCast_iff p 1 (P.q₁ s)).2 hp_modEq.of_mul_right]

/-- If `w` is a finite place of `E` above a prime `p ≡ 1` modulo `q₁ d`, then no infinite place `v`
of `E`, read as an element of `Gal(E/K)`, sends `w` to its complex conjugate `star w`. -/
lemma smul_ne_star (hp_modEq : p ≡ 1 [MOD P.q₁ s * P.d]) (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) :
    v • w ≠ star w := by
  -- the Frobenius element is trivial, so `(v, -1)` is not a power of it
  rw [Ne, smul_eq_star_iff_exists_frobElem_pow hp_mem (not_dvd_q₁_mul_d_of_modEq_one hp_modEq),
    frobElem_eq_one hp_modEq]
  simp

end Decomposition

end New.Parameters

end
