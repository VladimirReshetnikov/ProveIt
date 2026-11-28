import Lib.ClassField.Global.CMSplittingCharacters
import Lib.ClassField.HeckeCharacter.AlgebraicValues
import New.Derivatives.Field.PrimeDecomposition

/-!
# Weil data of the CM field E = K(ζ) and the number s₀

Let `K = ℚ(√-d) ⊆ ℂ` and `E = P.E s = K(ζ)`, with `ζ` a primitive root of unity of order `q₁`;
`star` is complex conjugation on `E`. The infinite places `v` of `E` form a group isomorphic to
`Gal(E/K)` and to `(ℤ/q₁)ˣ`, and `v • w` is the pullback of a finite place `w` along the
automorphism `P.galOfPlace s v`. This file describes the places of `E` above a prime
`p ≡ 1` mod `q₁ d` and builds the Weil data of `E`. From the idele α of these data it defines the
number s₀ = `New.Parameters.vacuumRoot`, a root of `(chiFin α)⁻¹`, and computes the absolute
values of its conjugates over `K`.

## Main definitions and results

* `New.Parameters.q_eq_of_modEq_one`, `New.Parameters.nonempty_infinitePlace_equiv_finPlace`: for
  `p ≡ 1` mod `q₁ d` the places above `p` have norm `p`. If `a ∈ 𝓞 E` has `a ā = p c` with `c : ℕ`
  prime to `p`, those that divide `a` are in bijection with the infinite places.
* `New.Parameters.α`: the idele with component 1/P'(ζ) at the places that divide
  `New.Parameters.betaKInE` and 1 elsewhere.
* `New.Parameters.instWeilDataE`: the Weil data, with ȷ = −1/√−d.
* `New.Parameters.norm_gal_vacuumRoot`: for every automorphism `σ` of `ℂ` over `K`, ‖σ s₀‖ ^ 2 is
  the root discriminant of `E` divided by `√d`.

Notions from other files:
* `New.Parameters`: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a prime `d` with
  `d ≡ q₀/2 - 1 mod q₀`; `New.Parameters.q₁` is `3 ^ c * 2 ^ s * q₀`, with `c = ⌊log₃ s⌋ + 5`.
* `New.Parameters.Φ`: `P.Φ s` is the group of infinite places of `E`. It is distinct from the bare
  `Φ` of the CM type of `E` (`New.CMType`): `Φ v : E →+* ℂ` is the embedding over `K` inducing `v`.
* `New.WeilData`: an imaginary element ȷ, a finite idele α and a splitting character υ.
* `New.chiFin`: the character x ↦ υ(x)|x|^(−1/2) of the finite ideles of `E`, x being extended by
  1 at infinity.
* `New.Parameters.relDifferentGen`: P'(ζ), the value at `ζ` of the derivative of the cyclotomic
  polynomial of order `q₁`; it generates the different of `E/K`.
-/

noncomputable section

namespace New.Parameters

/-!
## Places above a prime congruent to `1` modulo `q₁ d`

Such a prime `p` has trivial Frobenius element.
-/

section SplitPrimes

open NumberField IsDedekindDomain HeightOneSpectrum Ideal

variable {P : Parameters} {s p : ℕ} [hp : Fact p.Prime]

/-- Let `p ≡ 1` modulo `q₁ d` be prime and `w` a place of `E` above `p`. An infinite place `v`, read
as an element of `Gal(E/K)`, fixes `w` if and only if it is the identity. -/
lemma smul_eq_self_iff_eq_one {v : P.Φ s} {w : FinPlace (P.E s)}
    (hp_mod : p ≡ 1 [MOD P.q₁ s * P.d]) (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) :
    v • w = w ↔ v = 1 := by
  rw [smul_eq_self_iff_exists_frobElem_pow hp_mem (not_dvd_q₁_mul_d_of_modEq_one hp_mod),
    frobElem_eq_one hp_mod]
  simp

/-- If `p ≡ 1` modulo `q₁ d` is prime, every finite place `w` of `E` above `p` has absolute norm
`w.q = p`. -/
lemma q_eq_of_modEq_one {w : FinPlace (P.E s)} (hp_mod : p ≡ 1 [MOD P.q₁ s * P.d])
    (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) : w.q = p := by
  rw [q_eq_pow_orderOf_frobElem hp_mem (not_dvd_q₁_mul_d_of_modEq_one hp_mod),
    frobElem_eq_one hp_mod, orderOf_one,
    pow_one]

/-- Let `E = P.E s`, the field generated over `K` by a primitive `P.q₁ s`-th root of unity. Let `w`
be a finite place of `E` above a prime `p ≡ 1` modulo `P.q₁ s * P.d`. Let `a` in `𝓞 E` satisfy
`a * star a = p * c`, with `c` a natural number prime to `p`. Then `w` contains exactly one of `a`
and `star a`. -/
lemma star_mem_iff_notMem {w : FinPlace (P.E s)} (hp_mod : p ≡ 1 [MOD P.q₁ s * P.d])
    (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) {a : 𝓞 (P.E s)} {c : ℕ}
    (h_norm : a * star a = p * c) (h_coprime : p.Coprime c) :
    star a ∈ w.asIdeal ↔ a ∉ w.asIdeal := by
  have norm_mem : a * star a ∈ w.asIdeal := by simpa [h_norm] using mul_mem_right _ _ hp_mem
  refine ⟨fun h_star h_mem ↦ ?_, (w.isPrime.mem_or_mem norm_mem).resolve_left⟩
  -- if both `a` and `star a` lie in `w`, then `p * c` and hence `p` lie in `w ^ 2`
  have h_sq : (p * c : 𝓞 (P.E s)) ∈ w.asIdeal ^ 2 := by
    simpa [← h_norm, sq] using mul_mem_mul h_mem h_star
  rcases w.isPrime.mem_pow_mul _ h_sq with hp_sq | hc_mem
  · exact natCast_notMem_sq hp_mem (not_dvd_q₁_mul_d_of_modEq_one hp_mod) hp_sq
  · exact w.isPrime.notMem_of_isCoprime_of_mem h_coprime.cast hp_mem hc_mem

/-- Let `E = P.E s`, the field generated over `K = ℚ(√-d)` by a primitive `P.q₁ s`-th root of unity.
Let `p ≡ 1` modulo `P.q₁ s * P.d` be prime. Let `a` in `𝓞 E` satisfy `a * star a = p * c`, with `c`
a natural number prime to `p`. A finite place `w` of `E` above `p` that divides `a` divides it
exactly once: `w.intValuation a = exp (-1)`. -/
lemma intValuation_eq_of_mul_star {w : FinPlace (P.E s)} (hp_mod : p ≡ 1 [MOD P.q₁ s * P.d])
    (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal) {a : 𝓞 (P.E s)} {c : ℕ}
    (h_norm : a * star a = p * c) (h_coprime : p.Coprime c) (ha_mem : a ∈ w.asIdeal) :
    w.intValuation a = WithZero.exp (-1) := by
  -- in `a * star a = p * c`, both `star a` and `c` are units at `w`
  have val_star : w.intValuation (star a) = 1 := by
    rwa [intValuation_eq_one_iff, star_mem_iff_notMem hp_mod hp_mem h_norm h_coprime, not_not]
  have val_c : w.intValuation c = 1 :=
    intValuation_eq_one_iff.2 (w.isPrime.notMem_of_isCoprime_of_mem h_coprime.cast hp_mem)
  calc w.intValuation a = w.intValuation (a * star a) := by simp [val_star]
    _ = w.intValuation p := by simp [h_norm, val_c]
    _ = WithZero.exp (-1) := intValuation_natCast_eq_exp_neg_one hp_mem
      (not_dvd_q₁_mul_d_of_modEq_one hp_mod)

/-- Let `E = P.E s`, the field generated over `K` by a primitive `P.q₁ s`-th root of unity. Let `w`
be a finite place of `E` above a prime `p ≡ 1` modulo `P.q₁ s * P.d`. Let `u` and `v` be infinite
places in `P.Φ s`, read as elements of `Gal(E/K)`. If `v • w` is `u • w` or its conjugate
`star (u • w)`, then `u = v`. -/
lemma eq_of_smul_eq_or_smul_eq_star {u v : P.Φ s} {w : FinPlace (P.E s)}
    (hp_mod : p ≡ 1 [MOD P.q₁ s * P.d]) (hp_mem : (p : 𝓞 (P.E s)) ∈ w.asIdeal)
    (huv : v • w = u • w ∨ v • w = star (u • w)) : u = v := by
  -- `u⁻¹ * v` sends `u • w` to `v • w`; it cannot conjugate `u • w`, and fixes it only if trivial
  have hp_mem_smul : (p : 𝓞 (P.E s)) ∈ (u • w).asIdeal :=
    mem_asIdeal_smul_iff.2 (by simpa using hp_mem)
  have inv_mul_smul_smul : (u⁻¹ * v) • u • w = v • w := by
    simp [HeightOneSpectrum.ext_iff, Ideal.ext_iff, galOfPlaceInt, smul_smul]
  rw [← inv_mul_smul_smul, smul_eq_self_iff_eq_one hp_mod hp_mem_smul, inv_mul_eq_one] at huv
  exact huv.resolve_right (smul_ne_star hp_mod hp_mem_smul)

/-- Let `E = P.E s`, and let `p ≡ 1` modulo `P.q₁ s * P.d` be prime. Let `a` in `𝓞 E` satisfy
`a * star a = p * c`, where `star` is complex conjugation and `c` is a natural number prime to `p`.
Then the infinite places of `E` (the type `P.Φ s`) are in bijection with the finite places above `p`
that contain `a`. -/
lemma nonempty_infinitePlace_equiv_finPlace (hp_mod : p ≡ 1 [MOD P.q₁ s * P.d]) {a : 𝓞 (P.E s)}
    {c : ℕ} (h_norm : a * star a = p * c) (h_coprime : p.Coprime c) :
    Nonempty
      (P.Φ s ≃ {w : FinPlace (P.E s) // a ∈ w.asIdeal ∧ (p : 𝓞 (P.E s)) ∈ w.asIdeal}) := by
  classical
  -- Fix `w` above `p` and send `v` to the one of `v • w`, `star (v • w)` that contains `a`.
  obtain ⟨w, hw⟩ : ∃ w : FinPlace (P.E s), (p : 𝓞 (P.E s)) ∈ w.asIdeal :=
    FinPlace.exists_natCast_mem (P.E s) p
  have p_mem (v : P.Φ s) : (p : 𝓞 (P.E s)) ∈ (v • w).asIdeal :=
    mem_asIdeal_smul_iff.2 (by simpa using hw)
  have star_iff (v : P.Φ s) : a ∈ (star (v • w)).asIdeal ↔ a ∉ (v • w).asIdeal := by
    rw [mem_star_place, star_mem_iff_notMem hp_mod (p_mem v) h_norm h_coprime]
  let place (v : P.Φ s) : FinPlace (P.E s) := if a ∈ (v • w).asIdeal then v • w else star (v • w)
  have place_cases (v : P.Φ s) : place v = v • w ∨ place v = star (v • w) := ite_eq_or_eq _ _ _
  have place_mem (v : P.Φ s) : a ∈ (place v).asIdeal ∧ (p : 𝓞 (P.E s)) ∈ (place v).asIdeal := by
    by_cases ha_mem : a ∈ (v • w).asIdeal
    · rw [show place v = v • w from ite_eq_left ha_mem]
      exact ⟨ha_mem, p_mem v⟩
    · rw [show place v = star (v • w) from ite_eq_right ha_mem, star_iff, mem_star_place,
        star_natCast]
      exact ⟨ha_mem, p_mem v⟩
  refine ⟨.ofBijective (fun v ↦ ⟨place v, place_mem v⟩) ⟨fun u v huv ↦ ?_, fun w' ↦ ?_⟩⟩
  · -- `place u = place v` makes `v • w` equal to `u • w` or to its conjugate
    have place_eq : place u = place v := congrArg Subtype.val huv
    have h_or : v • w = u • w ∨ v • w = star (u • w) := by
      rcases place_cases u with hu | hu
      · rcases place_cases v with hv | hv
        · exact .inl (by rw [← hu, place_eq, hv])
        · exact .inr (by rw [← hu, place_eq, hv, star_star])
      · rcases place_cases v with hv | hv
        · exact .inr (by rw [← hu, place_eq, hv])
        · exact .inl (star_injective (by rw [← hu, place_eq, hv]))
    exact eq_of_smul_eq_or_smul_eq_star hp_mod hw h_or
  · -- `w'` is `v • w` or its conjugate for some `v`, and `a` lies in just one of the two
    obtain ⟨w', ha_mem, hp_mem⟩ := w'
    obtain ⟨v, rfl | rfl⟩ : ∃ v : P.Φ s, v • w = w' ∨ star (v • w) = w' :=
      exists_smul_eq_or_star hw hp_mem
    · exact ⟨v, Subtype.ext (ite_eq_left ha_mem)⟩
    · exact ⟨v, Subtype.ext (ite_eq_right ((star_iff v).1 ha_mem))⟩

end SplitPrimes

end New.Parameters

/-!
## The idele α and the Weil data of E

* `New.Parameters.v_alpha_mul_star_mul_relDifferentGen`: α·ᾱ·P'(ζ) is a unit at every finite place.
-/

section WeilDataOfE

open Ideal NumberField RingOfIntegers Polynomial IsDedekindDomain.HeightOneSpectrum NeZero Nat

namespace New

/-- The multiplicative map `E → 𝔸f E` that puts `x` at the places of `S` and `1` at the other
places. With `e` the idempotent of `S` it is `x ↦ e x + (1 - e)`. -/
noncomputable def diagonalAtPlaces {E : Type*} [Field E] [NumberField E] (S : Set (FinPlace E)) :
    E →* 𝔸f E where
  toFun x := idem S * algebraMap E (𝔸f E) x + (1 - idem S)
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul]
    linear_combination
      -(algebraMap E (𝔸f E) x - 1) * (algebraMap E (𝔸f E) y - 1) * idem_mul_self S

@[simp]
lemma diagonalAtPlaces_eq {E : Type*} [Field E] [NumberField E] (S : Set (FinPlace E)) (x : E) :
    diagonalAtPlaces S x = idem S * algebraMap E (𝔸f E) x + (1 - idem S) := rfl

open scoped Classical in
/-- The component of `diagonalAtPlaces S x` at `w` is `x` if `w ∈ S` and `1` otherwise. -/
lemma diagonalAtPlaces_apply {E : Type*} [Field E] [NumberField E] (S : Set (FinPlace E)) (x : E)
    (w : FinPlace E) :
    diagonalAtPlaces S x w = if w ∈ S then algebraMap E (𝔸f E) x w else 1 := by
  by_cases hw : w ∈ S <;> simp [hw]

end New

namespace New.Parameters

variable {P : Parameters} {s : ℕ}

/-- For every injective ring endomorphism `f` of `𝓞 (P.E s)` and every finite place `w` of
`E = P.E s`, the elements `f (P.relDifferentGen s)` and `P.relDifferentGen s` have the same `w`-adic
valuation. -/
lemma valuation_map_relDifferentGen (f : 𝓞 (P.E s) →+* 𝓞 (P.E s)) (hf : Function.Injective f)
    (w : FinPlace (P.E s)) :
    w.valuation (P.E s) (f (P.relDifferentGen s)).val =
      w.valuation (P.E s) (P.relDifferentGen s).val := by
  -- `f ζ` is again a primitive `q₁`-th root of unity, so `f relDifferentGen` and `relDifferentGen`
  -- both generate the different of `E / K`.
  have h_map : f (P.relDifferentGen s) =
      (cyclotomic (P.q₁ s) (𝓞 (P.E s))).derivative.eval (f (P.zetaInt s)) := by
    simp [← eval_map_apply, ← derivative_map]
  have h_span : span {f (P.relDifferentGen s)} = span {P.relDifferentGen s} := by
    rw [h_map, ← differentIdeal_eq_span_derivative_cyclotomic
      (isPrimitiveRoot_zetaInt.map_of_injective hf),
      differentIdeal_eq_span_relDifferentGen]
  simp only [coe_eq_algebraMap, valuation_of_algebraMap, intValuation_def, ← span_singleton_eq_bot,
    h_span]

/-- The generator `relDifferentGen` of the different of `E/K` has the same valuation at a finite
place `w` and at its conjugate `w̄`. -/
lemma valuation_star_relDifferentGen (w : FinPlace (P.E s)) :
    (star w).valuation (P.E s) (P.relDifferentGen s).val =
      w.valuation (P.E s) (P.relDifferentGen s).val := by
  rw [← valuation_map_relDifferentGen (starRingEnd _) star_injective (star w)]
  exact valuation_star w _

/-- A finite place that divides the generator `relDifferentGen` of the different of `E/K` divides
`betaKInE = (1 + √-d) / 2` or its conjugate. -/
lemma betaKInE_mem_or_star_mem {w : FinPlace (P.E s)} (h_mem : P.relDifferentGen s ∈ w.asIdeal) :
    P.betaKInE s ∈ w.asIdeal ∨ star (P.betaKInE s) ∈ w.asIdeal := by
  -- `relDifferentGen` divides `q₁`, whose primes divide `(d + 1) / 4 = betaKInE * star betaKInE`
  have h_q₁_dvd : P.q₁ s ∣ ((P.d + 1) / 4) ^ P.q₁ s := by
    have h_ne : (P.d + 1) / 4 ≠ 0 := by grind [P.sixty_four_lt_d]
    refine (Nat.dvd_pow_self_iff (NeZero.ne _) h_ne).2 fun q hq ↦ ?_
    obtain ⟨hq_prime, hq_dvd, -⟩ := mem_primeFactors.1 hq
    exact hq_prime.mem_primeFactors (P.dvd_d_add_one_div_four_of_dvd_q₁ hq_prime hq_dvd) h_ne
  have h_dvd : P.relDifferentGen s ∣ (P.betaKInE s * star (P.betaKInE s)) ^ P.q₁ s := by
    rw [star_betaKInE, betaKInE_mul_one_sub, ← cast_pow]
    exact relDifferentGen_dvd_q₁.trans (cast_dvd_cast h_q₁_dvd)
  exact w.isPrime.mem_or_mem (w.isPrime.mem_of_pow_mem _ (mem_of_dvd _ h_dvd h_mem))

/-- The finite idele `α` of `E`: its component is the inverse of the generator `relDifferentGen` of
the different of `E / K` at the places dividing `betaKInE = (1 + √-d) / 2`, and `1` at the other
places. -/
noncomputable def α (P : Parameters) (s : ℕ) : (𝔸f (P.E s))ˣ :=
  Units.map (diagonalAtPlaces {w : FinPlace (P.E s) | P.betaKInE s ∈ w.asIdeal})
    (Units.mk0 (P.relDifferentGen s).val (P.relDifferentGen_ne_zero s))⁻¹

open scoped Classical in
/-- At each finite place `w` of `E`, the component of the idele `α` is the image of the inverse of
`relDifferentGen` if `betaKInE ∈ w`, and `1` otherwise. -/
lemma alpha_apply (w : FinPlace (P.E s)) :
    (P.α s).val w = if P.betaKInE s ∈ w.asIdeal then
      algebraMap (P.E s) (𝔸f (P.E s)) (P.relDifferentGen s).val⁻¹ w else 1 :=
  diagonalAtPlaces_apply _ _ w

open scoped Classical in
/-- At each finite place `w` of `E`, the component of the idele `α⁻¹` is the image of
`relDifferentGen` if `betaKInE ∈ w`, and `1` otherwise. -/
lemma inv_alpha_apply (w : FinPlace (P.E s)) :
    (P.α s)⁻¹.val w = if P.betaKInE s ∈ w.asIdeal then
      algebraMap (P.E s) (𝔸f (P.E s)) (P.relDifferentGen s).val w else 1 :=
  diagonalAtPlaces_apply _ _ w

/-- The idele `α⁻¹` is integral: it lies in `Ô`, the finite adeles integral at every place. -/
lemma inv_alpha_mem : (P.α s)⁻¹.val ∈ Ô (P.E s) := by
  refine mem_Ô.2 fun w ↦ ?_
  rw [inv_alpha_apply]
  split_ifs <;> simp [valuation_le_one]

open scoped Classical in
/-- The valuation of `α` at `w` is the inverse of that of `relDifferentGen` if `w` divides
`betaKInE`, and `1` otherwise. -/
lemma v_alpha_apply (w : FinPlace (P.E s)) :
    Valued.v ((P.α s).val w) =
      if P.betaKInE s ∈ w.asIdeal then (w.valuation (P.E s) (P.relDifferentGen s).val)⁻¹ else
        1 := by
  rw [alpha_apply]
  split_ifs <;> simp

open scoped Classical in
/-- The valuation of `star α` (the complex conjugate of `α`) at `w` is the inverse of that of
`relDifferentGen` if `w` divides the conjugate `star betaKInE` of `betaKInE`, and `1` otherwise. -/
lemma v_star_alpha_apply (w : FinPlace (P.E s)) :
    Valued.v (star (P.α s).val w) = if star (P.betaKInE s) ∈ w.asIdeal then
      (w.valuation (P.E s) (P.relDifferentGen s).val)⁻¹ else 1 := by
  rw [finAdele_star_apply, v_conjLoc, v_alpha_apply, valuation_star_relDifferentGen]
  simp only [mem_star_place]

/-- Let `α = P.α s` be the finite idele of `E` whose component is `1 / P'(ζ)` at the places dividing
`betaKInE = (1 + √-d) / 2` and `1` elsewhere. At every finite place `w` the product
`α * star α.val * P'(ζ)` is a unit, where `star` is complex conjugation: its valuation equals
`1`. -/
lemma v_alpha_mul_star_mul_relDifferentGen (w : FinPlace (P.E s)) :
    Valued.v ((P.α s * star (P.α s).val * (P.relDifferentGen s).val) w) = 1 := by
  classical
  set t : WithZero (Multiplicative ℤ) := w.valuation (P.E s) (P.relDifferentGen s).val with ht
  have ht_ne : t ≠ 0 := by simp [ht]
  suffices h_cases : (if P.betaKInE s ∈ w.asIdeal then t⁻¹ else 1) *
      (if star (P.betaKInE s) ∈ w.asIdeal then t⁻¹ else 1) * t = 1 by
    rw [finAdele_mul_apply, finAdele_mul_apply, map_mul, map_mul, v_alpha_apply, v_star_alpha_apply]
    simpa [ht] using h_cases
  -- No place divides both `betaKInE` and its conjugate `1 - betaKInE`. At a place dividing one of
  -- them, one of `α`, `star α` cancels `relDifferentGen`; elsewhere `relDifferentGen` is a unit.
  split_ifs with h_mem h_star h_star
  · rw [star_betaKInE, w.asIdeal.sub_mem_iff_left h_mem] at h_star
    exact absurd h_star w.isPrime.one_notMem
  · rw [mul_one, inv_mul_cancel₀ ht_ne]
  · rw [one_mul, inv_mul_cancel₀ ht_ne]
  · rw [one_mul, one_mul]
    exact (valuation_eq_one_iff_notMem w).2 fun h ↦ (betaKInE_mem_or_star_mem h).elim h_mem h_star

/-- Let `α = P.α s` be the finite idele of `E` whose component is `1 / P'(ζ)` at the places dividing
`betaKInE = (1 + √-d) / 2` and `1` elsewhere. The order `q₁` of `ζ` is a denominator of `α`: the
product `q₁ α` lies in `Ô`, the finite adeles integral at every place. -/
lemma q₁_mul_alpha_mem : P.q₁ s * (P.α s).val ∈ Ô (P.E s) := by
  -- `q₁ = relDifferentGen * c` with `c` integral, and each component of `α` is `relDifferentGen⁻¹`
  -- or 1.
  obtain ⟨c, hc⟩ : P.relDifferentGen s ∣ P.q₁ s := relDifferentGen_dvd_q₁
  have h_adele : (P.q₁ s : 𝔸f (P.E s)) = (P.relDifferentGen s).val * c.val := by
    simpa using congrArg (fun x : 𝓞 (P.E s) ↦ algebraMap (P.E s) (𝔸f (P.E s)) x.val) hc
  refine mem_Ô.2 fun w ↦ ?_
  rw [h_adele, finAdele_mul_apply, map_mul, v_alpha_apply]
  split_ifs
  · -- the component is `c`
    simpa [field] using valuation_le_one (K := P.E s) w c
  · -- the component is `relDifferentGen * c`
    simpa using valuation_le_one (K := P.E s) w (P.relDifferentGen s * c)

/-- The order `q₁` of `ζ` is a multiple of `12`. -/
lemma twelve_dvd_q₁ : 12 ∣ P.q₁ s :=
  (show 12 ∣ 18480 by norm_num).trans (P.dvd_q₀.mul_right (towerDeg s))

/-- The powers of `ζ`, that is the roots of unity of `E` (see `exists_zeta_pow_eq`), have norm `1`
over `K`. -/
lemma norm_zeta_pow_eq_one (k : ℕ) : Algebra.norm P.K (P.ζ s ^ k) = 1 := by
  have h_ne_two : P.q₁ s ≠ 2 := fun h ↦ by simpa [h] using twelve_dvd_q₁ (P := P) (s := s)
  rw [map_pow, isPrimitiveRoot_zeta.norm_eq_one h_ne_two (P.irreducible_cyclotomic s), one_pow]

/-- For the chosen primitive `q₁`-th root of unity `ζ` of `E = K(ζ)`, the element `ζ - 1` has norm
`1` over `K`. -/
lemma norm_zeta_sub_one_eq_one : Algebra.norm P.K (P.ζ s - 1) = 1 := by
  -- The norm is the value at 1 of the cyclotomic polynomial, which is 1 because `q₁`, a multiple
  -- of 2 and of 3, is no prime power.
  have h_dvd : 12 ∣ P.q₁ s := twelve_dvd_q₁
  have h_two_lt : 2 < P.q₁ s := lt_of_lt_of_le (by norm_num) (le_of_dvd (NeZero.pos _) h_dvd)
  have h_not_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : p ^ k ≠ P.q₁ s := by
    intro h_eq
    rw [← h_eq] at h_dvd
    have h_two : 2 = p := prime_eq_prime_of_dvd_pow prime_two hp (.trans (by norm_num) h_dvd)
    have h_three : 3 = p := prime_eq_prime_of_dvd_pow prime_three hp (.trans (by norm_num) h_dvd)
    omega
  rw [isPrimitiveRoot_zeta.sub_one_norm_eq_eval_cyclotomic h_two_lt (P.irreducible_cyclotomic s),
    eval_one_cyclotomic_not_prime_pow h_not_prime_pow, Int.cast_one]

/-- For parameters `P` and a level `s`, every root of unity of the CM field `E = P.E s = K(ζ)`,
with `K = ℚ(√-d)`, is `δ / δ̄` for a unit `δ` of norm `1` over `K`. Here `star` is complex
conjugation, and the norm is written as the product, over the infinite places `w` of `E`, of the
images of `δ` under the embeddings `Φ w : E → ℂ` over `K` chosen at these places. -/
lemma exists_unit_prod_phi_eq_one_and_mul_star_eq (y : P.E s) (hy : IsOfFinOrder y) :
    ∃ δ : (𝓞 (P.E s))ˣ, ∏ w : InfinitePlace (P.E s), Φ w (δ : P.E s) = 1 ∧
      y * star (δ : P.E s) = δ := by
  -- With `y = ζ ^ k` take `δ = η ^ k`, where `η = i (ζ - 1)`, `i = ζ ^ m` and `q₁ = 4 m`.
  obtain ⟨k, -, rfl⟩ := exists_zeta_pow_eq hy
  obtain ⟨m, hm⟩ : 4 ∣ P.q₁ s := (show 4 ∣ 12 by norm_num).trans twelve_dvd_q₁
  let η : 𝓞 (P.E s) := P.zetaInt s ^ m * (P.zetaInt s - 1)
  have hη_val : η.val = P.ζ s ^ m * (P.ζ s - 1) := rfl
  have hη_norm : Algebra.norm P.K η.val = 1 := by
    rw [hη_val, map_mul, norm_zeta_pow_eq_one, norm_zeta_sub_one_eq_one, one_mul]
  have hη_norm_int : RingOfIntegers.norm P.K η = 1 := ext hη_norm
  have hη_unit : IsUnit η := (isUnit_norm P.K).1 (by simp [hη_norm_int])
  have hi_sq : P.ζ s ^ m * P.ζ s ^ m = -1 := by
    rw [← pow_add]
    exact (isPrimitiveRoot_zeta.pow (NeZero.pos _) (by omega)).eq_neg_one_of_two_right
  have hi_star : star (P.ζ s ^ m) = -P.ζ s ^ m := by
    rw [star_pow, star_zeta, inv_pow]
    exact inv_eq_of_mul_eq_one_right (by linear_combination -hi_sq)
  have hη_star : P.ζ s * star η.val = η.val := by
    rw [hη_val, star_mul', hi_star, star_sub, star_one, star_zeta]
    linear_combination -P.ζ s ^ m * mul_inv_cancel₀ (isPrimitiveRoot_zeta.ne_zero (ne (P.q₁ s)))
  have hδ_val : ((hη_unit.unit ^ k : (𝓞 (P.E s))ˣ) : P.E s) = η.val ^ k := by simp
  refine ⟨hη_unit.unit ^ k, ?_, by rw [hδ_val, star_pow, ← mul_pow, hη_star]⟩
  rw [prod_phi_eq_norm, hδ_val, map_pow, hη_norm, one_pow, OneMemClass.coe_one]

/-- Let `α = P.α s` be the finite idele of `E` whose component is `1 / P'(ζ)` at the places dividing
`betaKInE = (1 + √-d) / 2` and `1` elsewhere. At every finite place `w` of `E`, the order of
`(-1/√-d) α ᾱ` is minus the order `m` of the different of `E/ℚ`: its multiplicative valuation is
`exp m`. -/
lemma v_neg_inv_sqrtNegDInE_mul_alpha_mul_star (w : FinPlace (P.E s)) :
    Valued.v ((algebraMap (P.E s) (𝔸f (P.E s)) (-(P.sqrtNegDInE s).val⁻¹) * (P.α s).val *
        star (P.α s).val) w) =
      WithZero.exp (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 (P.E s))) : ℤ) := by
  -- The different is generated by `P'(ζ) √-d`, and `α * star α * P'(ζ)` is a local unit.
  have h_different :
      w.valuation (P.E s) (P.relDifferentGen s).val * w.valuation (P.E s) (P.sqrtNegDInE s).val =
        WithZero.exp (-(multiplicity w.asIdeal (differentIdeal ℤ (𝓞 (P.E s))) : ℤ)) := by
    rw [differentIdeal_eq_span_relDifferentGen_mul, ← w.intValuation_eq_exp_neg_multiplicity
      (ne_zero_of_differentIdeal_eq_span differentIdeal_eq_span_relDifferentGen_mul), map_mul]
    exact congrArg₂ HMul.hMul (valuation_of_algebraMap w _) (valuation_of_algebraMap w _)
  have h_unit : Valued.v ((P.α s).val w) * Valued.v (star (P.α s).val w) =
      (w.valuation (P.E s) (P.relDifferentGen s).val)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa using v_alpha_mul_star_mul_relDifferentGen w)
  have h_sqrt : Valued.v (algebraMap (P.E s) (𝔸f (P.E s)) (-(P.sqrtNegDInE s).val⁻¹) w) =
      (w.valuation (P.E s) (P.sqrtNegDInE s).val)⁻¹ := by simp
  rw [finAdele_mul_apply, finAdele_mul_apply, map_mul, map_mul, h_sqrt, mul_assoc, h_unit,
    ← mul_inv, mul_comm, h_different, WithZero.exp_neg, inv_inv]

/-- `-1/√(-d)`, the idele `α` and a splitting character `υ` are Weil data for `E`. The character
`υ` exists because every root of unity is `δ / δ̄` for a unit `δ` of norm `1` over `K`. -/
noncomputable instance instWeilDataE : WeilData (P.E s) :=
  letI : SplittingChar (P.E s) :=
    (nonempty_splittingChar exists_unit_prod_phi_eq_one_and_mul_star_eq).some
  { j := -(P.sqrtNegDInE s).val⁻¹
    star_j := by simp [← map_star_CM]
    im_pos := by simp [pos]
    α := P.α s
    self_dual := v_neg_inv_sqrtNegDInE_mul_alpha_mul_star
    isIntegral_traceOne := by simp [sqrtNegDInE, map_ofNat, isIntegral_coe]
    υ_inert := Cohomology.upsilon_atUniformizer_eq_neg_one }

/-- The purely imaginary element `ȷ` of the Weil data of `E` is `-1/√(-d)`. -/
lemma weilData_j_eq : (WeilData.j : P.E s) = -(P.sqrtNegDInE s : P.E s)⁻¹ := rfl

/-- Every embedding of the CM type sends `ȷ` to `i / √d`. -/
lemma phi_weilData_j (τ : P.Φ s) : Φ τ (WeilData.j : P.E s) = Complex.I / √P.d := by
  have h_sqrt : Φ τ (P.sqrtNegDInE s : P.E s) = Complex.I * √P.d := by
    simp
  rw [weilData_j_eq, map_neg, map_inv₀, h_sqrt, mul_inv, Complex.inv_I, neg_mul, neg_neg,
    div_eq_mul_inv]

/-- The number `(1 - ȷ⁻¹) / 2` is the generator `(1 + √(-d)) / 2` of the integers of `K`. -/
lemma traceOne_eq_betaKInE : (WeilData.traceOne : P.E s) = P.betaKInE s := by
  simp [WeilData.traceOne, weilData_j_eq, sqrtNegDInE, map_ofNat]

/-- Let `𝔞₀` be the ideal of the idele `α`. Then `ȷ 𝔞₀ 𝔞̄₀` is the inverse different of `E`: at
every finite place `w` the order of `ȷ α ᾱ` is minus the order of the different. -/
lemma v_weilData_j_mul_alpha_mul_star (w : FinPlace (P.E s)) :
    Valued.v ((algebraMap (P.E s) (𝔸f (P.E s)) WeilData.j * (P.α s).val * star (P.α s).val) w) =
      WithZero.exp (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 (P.E s))) : ℤ) :=
  WeilData.self_dual w

end New.Parameters

end WeilDataOfE

/-!
## The number s₀ and the absolute values of its conjugates

The number s₀ = `New.Parameters.vacuumRoot` is the principal `f`-th root of `(chiFin α)⁻¹`, where
`f` is the number of infinite places of `E`.
-/

namespace New.Parameters

open NumberField Finset Circle InfinitePlace

/-- The principal f-th root of the complex number (chiFin α)⁻¹ = υ(α)⁻¹|α|^(1/2), where
α = `New.Parameters.α`, υ is the splitting character of the Weil data of E, |α| is the idele norm
and f is the number of infinite places of E. -/
noncomputable def vacuumRoot (P : Parameters) (s : ℕ) : ℂ :=
  (chiFin (α P s))⁻¹ ^ (Core.numInfPlaces (P.E s) : ℂ)⁻¹

/-- The power of `s₀ = vacuumRoot P s` by the number of infinite places of `E` is `(chiFin α)⁻¹`,
where `chiFin α = υ(α) |α|^(-1/2)` for the idele `α` and the splitting character `υ` of `E`. -/
lemma vacuumRoot_pow_numInfPlaces (P : Parameters) (s : ℕ) :
    vacuumRoot P s ^ Core.numInfPlaces (P.E s) = (chiFin (P.α s))⁻¹ := by
  rw [vacuumRoot, Complex.cpow_nat_inv_pow _ Fintype.card_ne_zero]

/-- A positive power of `chiFin α` lies in `K`: it is the norm to `K` of an element of `E`. -/
lemma exists_chiFin_alpha_pow_mem (P : Parameters) (s : ℕ) :
    ∃ k : ℕ, 0 < k ∧ chiFin (P.α s) ^ k ∈ K P := by
  obtain ⟨k, hk, y, -, hy⟩ := WeilData.exists_chiFin_pow_eq_prod (P.α s)
  have h_norm : chiFin (P.α s) ^ k = Algebra.norm P.K (starRingEnd (P.E s) y) := by
    rw [hy, prod_phi_eq_norm]
  exact ⟨k, hk, by simp [h_norm]⟩

/-- A positive power of `s₀ = vacuumRoot P s`, a root of `(chiFin α)⁻¹`, lies in `K = ℚ(√-d)`. -/
lemma exists_vacuumRoot_pow_mem (P : Parameters) (s : ℕ) :
    ∃ n : ℕ, 0 < n ∧ vacuumRoot P s ^ n ∈ K P := by
  obtain ⟨k, hk, h_mem⟩ : ∃ k : ℕ, 0 < k ∧ chiFin (P.α s) ^ k ∈ K P :=
    exists_chiFin_alpha_pow_mem P s
  refine ⟨Core.numInfPlaces (P.E s) * k, Nat.mul_pos Fintype.card_pos hk, ?_⟩
  simpa [pow_mul, vacuumRoot_pow_numInfPlaces] using h_mem

/-- The idele norm of the finite idele `α = P.α s`, extended by `1` at infinity, is the product of
the absolute values of the generator `relDifferentGen` of the different of `E/K` at all infinite
places `v` of `E` (the type `P.Φ s`). -/
lemma ideleAbs_alpha_eq_prod (P : Parameters) (s : ℕ) :
    ideleAbs (finIdeleIncl (P.α s)) = ∏ v : P.Φ s, v (P.relDifferentGen s).val := by
  -- `α * star α * relDifferentGen` is a unit at all finite places, so its idele norm comes from the
  -- infinite places, while `relDifferentGen` has idele norm one (product formula).
  let a : (𝔸 (P.E s))ˣ := finIdeleIncl (P.α s)
  let y : (P.E s)ˣ := .mk0 (P.relDifferentGen s).val (P.relDifferentGen_ne_zero s)
  let x : (𝔸 (P.E s))ˣ := a * star a * y.map (toAdele (E := P.E s))
  have h_unit (w : FinPlace (P.E s)) : Valued.v (x.val.snd w) = 1 := by
    simpa [x, a, y] using v_alpha_mul_star_mul_relDifferentGen w
  refine (pow_left_inj₀ (by simp [ideleAbs_nonneg_and_ne_zero]) (by positivity) two_ne_zero).1 ?_
  calc ideleAbs a ^ 2 = ideleAbs x := by
        rw [map_mul, map_mul, ideleAbs_star, ideleAbs_toAdele, mul_one, sq]
    _ = ∏ v : P.Φ s, ‖x.val.fst v‖ ^ 2 := ideleAbs_eq_prod_of_v_eq_one h_unit
    _ = (∏ v : P.Φ s, v (P.relDifferentGen s).val) ^ 2 := by simp [x, a, y, prod_pow, ← apply]

/-- Let `E = K(ζ)` with `K = ℚ(√-d)`, and let `f` be the number of infinite places of `E`. Let
`α = P.α s` be the finite idele of `E` with component `1 / P'(ζ)` at the places dividing
`(1 + √-d) / 2` and `1` elsewhere. The number `s₀ = vacuumRoot P s` is the principal `f`-th root of
`υ(α)⁻¹ |α|^(1/2)`, with `|α|` the idele norm. For every automorphism `σ` of `ℂ` over `K`, the
square `‖σ s₀‖ ^ 2` is the root discriminant of `E` divided by `√d`. -/
lemma norm_gal_vacuumRoot (P : Parameters) (s : ℕ) (σ : Gal(ℂ/K P)) :
    ‖σ (vacuumRoot P s)‖ ^ 2 = rootDiscr (P.E s) / √P.d := by
  -- A power of `s₀` lies in `K`, so `σ` fixes it and preserves the absolute value of `s₀`.
  have h_norm : ‖σ (vacuumRoot P s)‖ = ‖vacuumRoot P s‖ := by
    obtain ⟨n, hn_pos, h_mem⟩ : ∃ n : ℕ, 0 < n ∧ vacuumRoot P s ^ n ∈ K P :=
      exists_vacuumRoot_pow_mem P s
    have h_fixed : σ (vacuumRoot P s ^ n) = vacuumRoot P s ^ n := σ.commutes ⟨_, h_mem⟩
    rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn_pos.ne', ← norm_pow, ← map_pow, h_fixed,
      norm_pow]
  -- Raise both sides to the number `f` of infinite places. As `vacuumRoot ^ f = (chiFin α)⁻¹`, the
  -- left side becomes the idele norm of `α`; as `rootDiscr ^ f = ∏ v, v deltaE` and
  -- `v deltaE = v relDifferentGen * √d`, the right side becomes `∏ v, v relDifferentGen`.
  set f : ℕ := Core.numInfPlaces (P.E s) with hf
  have h_sqrt_pos : 0 < √(P.d : ℝ) := by simpa using NeZero.pos P.d
  have h_disc_pos : 0 < rootDiscr (P.E s) := rootDiscr_pos _
  rw [h_norm, ← pow_left_inj₀ (n := f) (by positivity) (by positivity) Fintype.card_ne_zero]
  calc (‖vacuumRoot P s‖ ^ 2) ^ f = (‖chiFin (P.α s)‖ ^ 2)⁻¹ := by
        rw [pow_right_comm, ← norm_pow, vacuumRoot_pow_numInfPlaces, norm_inv, inv_pow]
    _ = ideleAbs (finIdeleIncl (P.α s)) := by
        simp [chiFin, chiAdelic, norm_coe, ideleAbs_nonneg_and_ne_zero]
    _ = (∏ v : P.Φ s, v (P.deltaE s).val) / √P.d ^ f := by
        simp [ideleAbs_alpha_eq_prod, infinitePlace_apply_deltaE, prod_mul_distrib, hf,
          h_sqrt_pos.ne']
    _ = (rootDiscr (P.E s) / √P.d) ^ f := by rw [prod_deltaE_eq_rootDiscr_pow, div_pow]

end New.Parameters

end
