import Lib.Analytic.Primes
import New.Reduction.Data.AdmissibleData

/-!
# Admissible data exist at every large x

For every large integer `x`, this file constructs the data `New.Data`. It builds the ranks and the
field, the places, the scales and the primes in turn.

## Main definitions and results

* `New.Parameters.IsAdmissibleData`: admissible data, with explicit values of the ranks and scales
  and any `b`-places and primes that have the required properties.
* `New.eventually_exists_data_of_isAdmissibleData`: at every large `x` such data are the fields
  (`New.Data.HasFields`) of the data `New.Data`.
* `New.eventually_exists_data`: admissible data exist at every large `x`.

Notions from other files:
* `P : Parameters` fixes `q₀` and the prime `d` with `K = ℚ(√-d)`; at the exponent `s` it gives
  `P.q₁ s = q₀ * towerDeg s`, where `towerDeg s = 3 l₀ 2 ^ s` and `l₀ = 3 ^ (⌊log₃ s⌋ + 4)` is, for
  `s ≥ 1`, the least power of `3` above `27 s`.
* `P.Φ s` is the set of infinite places of the field `E = P.E s`, a group identified with `(ℤ/q₁)ˣ`;
  `P.placeOfInt s ν` is the place of the class of `ν`, and `P.placeClass` reduces this class modulo
  a divisor of `q₁`.
* `P.IsSparse s L T`: no places `σ, τ, ρ` in `T` have `τ / σ ≡ ± ℓ ^ i` and `ρ / σ ≡ ± ℓ ^ j` modulo
  the part of `q₁` prime to `ℓ`, for a prime `ℓ ≤ L` and `0 < i < j < l₀`.
* `P.q₂ s = (q₀ d) ^ (s + 6)`; its square, written `q₂²`, is the modulus of the primes to be found.
* `P.logLevelMin s m κ M L` is `log N₋`, where `N₋ = κ̄ ^ m (M rd_E / 2π) ^ (m - 1) b ^ (-15 / 2)`,
  `κ̄` being the geometric mean of the weights `κ`, `rd_E` the root discriminant and `L = log b`.

## Relation to the literature

Known result: Behrend's construction for several equations at once. Source: Shapira, Behrend-type
constructions for sets of linear equations, Acta Arith. 2006 (after Behrend, PNAS 32, 1946); compare
Alon–Shapira, A characterization of easily testable induced subgraphs (2006), Lemma 4.1 (preprint
numbering). Form here: all weights up to a given bound are avoided at once, modulo an
integer, with a fixed number of digits and the explicit count of points on a sphere. This concerns
`exists_three_term_free`.
-/

/-!
## Existence of admissible data at every large integer x

The ranks `m`, `r`, the exponent `s`, the field and the scales `x₁`, `b` come from `x`. The places
of weight `b` are `-g ^ e` with `g = 1 + 3 l₀ q₀` and `e` in a set of Behrend's type. The primes
`p₀`, `p₁` and `N` come from windows for primes in progressions, the element of norm `p₀ p₁` from
a pigeonhole argument in the class group of `K`, and the element of norm `N` from a sum of two
squares. The windows are those of `exists_prime_modEq_one_log_mem`, a consequence of the
Siegel–Walfisz theorem. That lemma needs an upper bound for the start of a window, so the upper
bound for `log N₋` is used as well.
-/

namespace New

open Finset Behrend Real Filter NumberField ClassGroup NeZero QuadField

/-- A sphere is strictly convex: if three integer vectors of equal squared length satisfy
`(α + α') v = α u + α' w` with `α, α' > 0`, they are equal. -/
lemma eq_of_add_mul_eq_of_sum_sq_eq {ι : Type*} [Fintype ι] {α α' : ℕ} {u v w : ι → ℕ}
    (hα : 0 < α) (hα' : 0 < α') (h_coord : ∀ l : ι, ((α : ℤ) + α') * v l = α * u l + α' * w l)
    (huv_sq : ∑ l : ι, u l ^ 2 = ∑ l : ι, v l ^ 2)
    (hvw_sq : ∑ l : ι, v l ^ 2 = ∑ l : ι, w l ^ 2) : u = v ∧ v = w := by
  -- the three squared lengths agree, so `α α' ∑ (u l - w l) ^ 2 = 0`
  have h_sq : ∑ l, (α * α' : ℤ) * (u l - w l : ℤ) ^ 2 = 0 := by
    zify at huv_sq hvw_sq
    calc _ = ∑ l, ((α + α') * (α * (u l : ℤ) ^ 2 + α' * (w l : ℤ) ^ 2) -
            ((α + α') * v l) ^ 2) := sum_congr rfl fun l _ ↦ by grind [h_coord l]
      _ = 0 := by
          simp only [mul_pow, sum_sub_distrib, sum_add_distrib, ← mul_sum, huv_sq, ← hvw_sq]
          ring
  obtain rfl : u = w := funext fun l ↦ by
    simpa [hα.ne', hα'.ne', sub_eq_zero] using
      (sum_eq_zero_iff_of_nonneg fun l _ ↦ by positivity).1 h_sq l (mem_univ l)
  have h_eq : u = v := funext fun l ↦ by nlinarith [h_coord l]
  exact ⟨h_eq, h_eq.symm⟩

/-- **Behrend's sets.** If `0 < L` and `(L H) ^ n ≤ o`, there is a set `S` of at least
`H ^ n / (n H ^ 2)` integers in `[0, o)` such that a congruence `(α + α') e₂ ≡ α e₁ + α' e₃`
modulo `o`, with `e₁, e₂, e₃ ∈ S`, `α, α' > 0` and `α + α' ≤ L`, forces `e₁ = e₂ = e₃`. -/
lemma exists_three_term_free {n H L o : ℕ} (hL : 0 < L) (ho : (L * H) ^ n ≤ o) :
    ∃ S : Finset ℕ,
      (∀ e ∈ S, e < o) ∧
      (H ^ n / (n * H ^ 2) : ℝ) ≤ #S ∧
      ∀ e₁ ∈ S, ∀ e₂ ∈ S, ∀ e₃ ∈ S, ∀ α α' : ℕ, 0 < α → 0 < α' → α + α' ≤ L →
        (α + α') * e₂ ≡ α * e₁ + α' * e₃ [MOD o] → e₁ = e₂ ∧ e₂ = e₃ := by
  -- Take the integers whose digits in base `L * H` form a vector on a large sphere in
  -- `{0, …, H - 1} ^ n`. A congruence between three of them is an equation between digit vectors,
  -- which makes one a mean of the other two; on a sphere this forces equality.
  obtain ⟨k, hk⟩ := exists_large_sphere n H
  -- `map (L * H) v` is the number with digits `v` in base `L * H`
  have h_lt (v : Fin n → ℕ) (hv : ∀ l : Fin n, v l < L * H) : map (L * H) v < o :=
    calc ∑ l : Fin n, v l * (L * H) ^ (l : ℕ) < (L * H) ^ n :=
          (finFunctionFinEquiv fun l : Fin n ↦ ⟨v l, hv l⟩).isLt
      _ ≤ o := ho
  have h_sphere {v : Fin n → ℕ} :
      v ∈ sphere n H k ↔ (∀ l : Fin n, v l < H) ∧ ∑ l : Fin n, v l ^ 2 = k := by
    simp [sphere, Behrend.mem_box]
  have h_digit (v : Fin n → ℕ) (hv : v ∈ sphere n H k) (l : Fin n) : v l < L * H :=
    ((h_sphere.1 hv).1 l).trans_le (Nat.le_mul_of_pos_left H hL)
  refine ⟨(sphere n H k).image (map (L * H)), forall_mem_image.2 fun v hv ↦ h_lt v (h_digit v hv),
    by simpa [card_image_of_injOn (map_injOn.mono h_digit)] using hk, ?_⟩
  simp only [forall_mem_image, h_sphere]
  rintro u ⟨hu, hu_sq⟩ v ⟨hv, hv_sq⟩ w ⟨hw, hw_sq⟩ α α' hα hα' h_sum h_cong
  -- both sides of the congruence have digits below `L * H`, so they are equal digit by digit
  have h_left (l : Fin n) : ((α + α') • v) l < L * H :=
    show (α + α') * v l < L * H by nlinarith [hv l]
  have h_right (l : Fin n) : (α • u + α' • w) l < L * H :=
    show α * u l + α' * w l < L * H by nlinarith [hu l, hw l]
  have h_mean : (α + α') • v = α • u + α' • w := by
    refine map_injOn h_left h_right (Nat.ModEq.eq_of_lt_of_lt ?_ (h_lt _ h_left) (h_lt _ h_right))
    simpa only [map_add, map_nsmul, smul_eq_mul] using h_cong
  exact (eq_of_add_mul_eq_of_sum_sq_eq hα hα' (fun l ↦ mod_cast congrFun h_mean l)
    (hu_sq.trans hv_sq.symm) (hv_sq.trans hw_sq.symm)).imp (congrArg _) (congrArg _)

/-- The infinite places `P.Φ s` of `E = P.E s` form the group `(ℤ/q₁)ˣ`, `q₁ = P.q₁ s`;
`P.placeOfInt s ν` is the place of the residue of an integer `ν` prime to `q₁`, and `P.placeClass`
reduces a place modulo a divisor of `q₁`. The place of `g = 1 + 3 l₀ q₀`, where `q₀ = P.q₀` and
`l₀ = 3 ^ (⌊log₃ s⌋ + 4)`, has order `2 ^ s` modulo some power `2 ^ (s + v)` that divides `q₁`. -/
lemma Parameters.exists_orderOf_placeClass_eq (P : Parameters) (s : ℕ) :
    ∃ (v : ℕ) (hv : 2 ^ (s + v) ∣ P.q₁ s),
      orderOf (P.placeClass hv (P.placeOfInt s (3 * l₀ s * P.q₀ + 1 : ℕ))) = 2 ^ s := by
  -- Write `q₀ = 2 ^ v u` with `u` odd and `v ≥ 2`; then `g = 1 + 2 ^ v (3 l₀ u)`.
  obtain ⟨v, u, hu, hq₀⟩ : ∃ v u : ℕ, Odd u ∧ P.q₀ = 2 ^ v * u :=
    Nat.exists_eq_two_pow_mul_odd (ne P.q₀)
  have h_four : 2 ^ 2 ∣ 2 ^ v * u := (Nat.dvd_trans (by norm_num) P.dvd_q₀).trans hq₀.dvd
  have h_two_le : 2 ≤ v := (Nat.pow_dvd_pow_iff_le_right one_lt_two).1
    ((hu.coprime_two_left.pow_left 2).dvd_of_dvd_mul_right h_four)
  set a : ℕ := 3 * l₀ s * u with ha
  have ha_odd : Odd a := by simp [ha, l₀, Nat.odd_mul, Nat.odd_pow_iff, hu, Nat.odd_iff.2]
  have h_order : orderOf (1 + 2 ^ v * (a : ℤ) : ZMod (2 ^ (s + v))) = 2 ^ s :=
    ZMod.orderOf_one_add_mul_prime_pow Nat.prime_two v (by omega) (by omega) a
      (mod_cast ha_odd.not_two_dvd_nat) s
  refine ⟨v, ⟨a, by grind [towerDeg_eq]⟩, ?_⟩
  rw [← orderOf_units, P.placeClass_placeOfInt (by simp [isCoprime_one_left]), ← h_order, hq₀, ha]
  push_cast
  ring_nf

/-- Let `y` be a place whose class modulo the part of `q₁` prime to the prime `ℓ` is `± ℓ ^ i`.
Then the square of its class modulo every divisor of `q₁` prime to `ℓ` is `ℓ ^ (2 i)`. -/
lemma Parameters.placeClass_sq_eq (P : Parameters) {s ℓ i q : ℕ} (hℓ : ℓ.Prime) {y : P.Φ s} {ε : ℤˣ}
    (hy : (P.placeClass (Nat.ordCompl_dvd (P.q₁ s) ℓ) y).val = (ε : ℤ) * ℓ ^ i) (hq : q ∣ P.q₁ s)
    (h_coprime : ℓ.Coprime q) : (P.placeClass hq y).val ^ 2 = (ℓ : ZMod q) ^ (2 * i) := by
  have h_dvd : q ∣ ordCompl[ℓ] (P.q₁ s) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd hq (hℓ.coprime_iff_not_dvd.1 h_coprime)
  have h_val : (P.placeClass hq y).val =
      ZMod.castHom h_dvd (ZMod q) (P.placeClass (Nat.ordCompl_dvd (P.q₁ s) ℓ) y).val := by
    rw [Parameters.placeClass, ← ZMod.unitsMap_comp h_dvd (Nat.ordCompl_dvd (P.q₁ s) ℓ)]
    simp [Parameters.placeClass, ZMod.unitsMap_def]
  rw [h_val, hy, map_mul, map_pow, map_intCast, map_natCast, mul_pow, ← Int.cast_pow,
    Int.isUnit_sq ε.isUnit, Int.cast_one, one_mul, ← pow_mul']

/-- In a commutative group, `(g ^ e₂ / g ^ e₁) ^ (a + b) = (g ^ e₃ / g ^ e₁) ^ b` forces
`(a + b) e₂ ≡ a e₁ + b e₃` modulo the order of `g`. -/
lemma modEq_orderOf_of_div_pow_eq {G : Type*} [CommGroup G] {g : G} {e₁ e₂ e₃ a b : ℕ}
    (h_eq : (g ^ e₂ / g ^ e₁) ^ (a + b) = (g ^ e₃ / g ^ e₁) ^ b) :
    (a + b) * e₂ ≡ a * e₁ + b * e₃ [MOD orderOf g] := by
  refine Nat.ModEq.add_right_cancel' (e₁ * b) (pow_eq_pow_iff_modEq.1 ?_)
  rw [div_pow, div_pow, div_eq_div_iff_mul_eq_mul] at h_eq
  calc g ^ ((a + b) * e₂ + e₁ * b) = g ^ (e₃ * b + e₁ * (a + b)) := by
        simpa only [← pow_mul, ← pow_add, mul_comm e₂] using h_eq
    _ = g ^ (a * e₁ + b * e₃ + e₁ * b) := by ring_nf

/-- If `(2 l₀ H) ^ n ≤ 2 ^ s` and `2 l₀ (L + 1) < 2 ^ s`, there is a set of at least
`H ^ n / (n H ^ 2)` places of class `-1` modulo `q₀` that is sparse for the primes `ℓ ≤ L`: it has
no places `σ, τ, ρ` with `τ / σ ≡ ± ℓ ^ i` and `ρ / σ ≡ ± ℓ ^ j`, `0 < i < j < l₀`, modulo the part
of `q₁` prime to `ℓ`. -/
lemma Parameters.exists_large_isSparse (P : Parameters) {s n H L : ℕ}
    (h_room : (2 * l₀ s * H) ^ n ≤ 2 ^ s) (hL : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ T : Finset (P.Φ s),
      (∀ σ ∈ T, P.placeClass (P.q₀.dvd_mul_right (towerDeg s)) σ = -1) ∧
      (H ^ n / (n * H ^ 2) : ℝ) ≤ #T ∧
      P.IsSparse s L T := by
  -- Take the places `-g ^ e`, with `g = 1 + 3 l₀ q₀` and `e` in Behrend's set to base `2 l₀ H`.
  -- For `ℓ = 2` these have no ratio `± ℓ ^ i` modulo `3 l₀`. For odd `ℓ`, three of them in a
  -- forbidden position give a congruence between their exponents, which Behrend's set allows only
  -- if they are equal; then `ℓ ^ (2 i) ≡ 1`, which is false as `ℓ` has a large order.
  let g : P.Φ s := P.placeOfInt s (3 * l₀ s * P.q₀ + 1 : ℕ)
  obtain ⟨v, hv, h_order_g⟩ := P.exists_orderOf_placeClass_eq s
  let ψ : P.Φ s →* (ZMod (2 ^ (s + v)))ˣ := P.placeClass hv
  -- Behrend's set `S` of exponents below the order of `ψ g`, for the weights up to `2 l₀`
  obtain ⟨S, h_lt, h_card, h_free⟩ := exists_three_term_free (o := orderOf (ψ g))
    (by linarith [mul_lt_l₀ s]) (h_room.trans h_order_g.ge)
  -- the places `-g ^ e` are distinct modulo `2 ^ (s + v)`, and `≡ -1` modulo `3 l₀ q₀`
  let place (e : ℕ) : P.Φ s := P.placeOfInt s (-1) * g ^ e
  have h_inj : Set.InjOn place S := fun e he e' he' h ↦
    pow_injOn_Iio_orderOf (x := ψ g) (h_lt e he) (h_lt e' he')
      (by simpa only [map_pow] using congrArg ψ (mul_left_cancel h))
  have h_class {q : ℕ} (hq : q ∣ P.q₁ s) (hq' : q ∣ 3 * l₀ s * P.q₀) (e : ℕ) :
      P.placeClass hq (place e) = -1 := by
    rw [Units.ext_iff, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      P.placeClass_placeOfInt isCoprime_one_left.neg_left,
      P.placeClass_placeOfInt (by simp [isCoprime_one_left]), Int.cast_natCast, Nat.cast_succ,
      (ZMod.natCast_eq_zero_iff _ q).2 hq']
    simp
  refine ⟨S.image place, forall_mem_image.2 fun e _ ↦ h_class _ (dvd_mul_left P.q₀ (3 * l₀ s)) e,
    by rwa [card_image_of_injOn h_inj], ?_⟩
  rintro ℓ hℓ hℓL i j hi hij hj φ ⟨σ, hσ, τ, hτ, ρ, hρ, ε, ε', h_ratio_i, h_ratio_j⟩
  obtain ⟨e₁, he₁, rfl⟩ := mem_image.1 hσ
  obtain ⟨e₂, he₂, rfl⟩ := mem_image.1 hτ
  obtain ⟨e₃, he₃, rfl⟩ := mem_image.1 hρ
  obtain rfl | h_odd := hℓ.eq_two_or_odd'
  · -- `ℓ = 2`: modulo `3 l₀ = 3 ^ c` the ratio is `1`, so `4 ^ i ≡ 1`; but `4` has order `l₀ > i`
    set c : ℕ := Nat.log 3 s + 5
    have h_dvd : 3 ^ c ∣ P.q₁ s := Dvd.dvd.mul_left (dvd_mul_right ..) P.q₀
    have h_dvd' : 3 ^ c ∣ 3 * l₀ s * P.q₀ := ⟨P.q₀, by rw [l₀, ← pow_succ']⟩
    have h_four : (1 + 3 : ZMod (3 ^ c)) ^ i = 1 := by
      have h_sq := P.placeClass_sq_eq hℓ h_ratio_i h_dvd (.pow_right c (by norm_num))
      norm_num [map_div, h_class h_dvd h_dvd', pow_mul] at h_sq ⊢
      exact h_sq.symm
    have h_order : orderOf (1 + 3 : ZMod (3 ^ c)) = l₀ s :=
      ZMod.orderOf_one_add_prime Nat.prime_three (by norm_num) _
    linarith [orderOf_le_of_pow_eq_one hi h_four]
  · -- `ℓ` odd: modulo `2 ^ (s + v)`, the `2 j`-th power of the first ratio and the `2 i`-th
    -- power of the second are both `ℓ ^ (2 i j)`
    have h_coprime_two (k : ℕ) : ℓ.Coprime (2 ^ k) := .pow_right _ (by simpa using h_odd)
    have h_sq_i : (ψ (place e₂ / place e₁)).val ^ 2 = (ℓ : ZMod (2 ^ (s + v))) ^ (2 * i) :=
      P.placeClass_sq_eq hℓ h_ratio_i hv (h_coprime_two _)
    have h_sq_j : (ψ (place e₃ / place e₁)).val ^ 2 = (ℓ : ZMod (2 ^ (s + v))) ^ (2 * j) :=
      P.placeClass_sq_eq hℓ h_ratio_j hv (h_coprime_two _)
    have h_rel : ψ (place e₂ / place e₁) ^ (2 * j) = ψ (place e₃ / place e₁) ^ (2 * i) := by
      simp only [Units.ext_iff, Units.val_pow_eq_pow_val, pow_mul _ 2, h_sq_i, h_sq_j]
      ring
    -- compare exponents of `g`: `2 j e₂ ≡ 2 (j - i) e₁ + 2 i e₃`
    obtain ⟨a, ha, rfl⟩ : ∃ a > 0, a + i = j := ⟨j - i, by omega, by omega⟩
    have h_cong : (2 * a + 2 * i) * e₂ ≡ 2 * a * e₁ + 2 * i * e₃ [MOD orderOf (ψ g)] := by
      have h_ψ (e : ℕ) : ψ (place e / place e₁) = ψ g ^ e / ψ g ^ e₁ := by
        simp only [place, mul_div_mul_left_eq_div, map_div, map_pow]
      exact modEq_orderOf_of_div_pow_eq (by rwa [← h_ψ e₂, ← h_ψ e₃, ← mul_add])
    obtain ⟨rfl, -⟩ : e₁ = e₂ ∧ e₂ = e₃ :=
      h_free e₁ he₁ e₂ he₂ e₃ he₃ (2 * a) (2 * i) (by omega) (by omega) (by omega) h_cong
    -- so `2 ^ (s + 1) ∣ ℓ ^ (2 i) - 1`, and the order of `ℓ` is too large for that
    have h_pow : (ℓ : ZMod (2 ^ (s + 1))) ^ (2 * i) = 1 := by
      simpa using (P.placeClass_sq_eq hℓ h_ratio_i P.two_pow_dvd_q₁ (h_coprime_two _)).symm
    have h_order : 2 ^ s ≤ (ℓ + 1) * (2 * i) :=
      two_pow_le_of_pow_eq_one (q := ℓ) hℓ.one_lt (by omega) (by simpa using h_pow)
    have h_small : (ℓ + 1) * (2 * i) ≤ (L + 1) * (2 * l₀ s) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith only [h_order, h_small, hL]

/-- **A large sparse set of places.** The infinite places `P.Φ s` of `E = P.E s` form the group
`(ℤ/q₁)ˣ`. Let `0 < n`, `1 ≤ W ≤ 2 ^ s ≤ W ^ n`, `(2 l₀) ^ n ≤ W`, `3 l₀ n 2 ^ n ≤ W ^ 3` and
`2 l₀ (L + 1) < 2 ^ s`. There is a set of at least `towerDeg s / W ^ 6` places of class `-1` modulo
`q₀` that is sparse for the primes `ℓ ≤ L`: it has no places `σ, τ, ρ` with `τ / σ ≡ ± ℓ ^ i` and
`ρ / σ ≡ ± ℓ ^ j`, `0 < i < j < l₀`, modulo the part of `q₁` prime to `ℓ`. -/
lemma Parameters.exists_isSparse (P : Parameters) {s n L : ℕ} {W : ℝ} (hn : 0 < n) (hW : 1 ≤ W)
    (h_lower : W ≤ 2 ^ s) (h_upper : 2 ^ s ≤ W ^ n) (h_room : (2 * l₀ s) ^ n ≤ W)
    (h_count : 3 * l₀ s * n * 2 ^ n ≤ W ^ 3) (hL : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ T : Finset (P.Φ s),
      (∀ σ ∈ T, P.placeClass (P.q₀.dvd_mul_right (towerDeg s)) σ = -1) ∧
      towerDeg s ≤ #T * W ^ 6 ∧
      P.IsSparse s L T := by
  have hW_pos : 0 < W := one_pos.trans_le hW
  -- the side `H = 2 ^ k` of Behrend's cube has `H ^ n ≤ 2 ^ s / W < (2 H) ^ n`, so `H ≤ W`
  obtain ⟨k, hk_lower, hk_upper⟩ :
      ∃ k : ℕ, (2 ^ n) ^ k ≤ 2 ^ s / W ∧ 2 ^ s / W < (2 ^ n) ^ (k + 1) :=
    exists_nat_pow_near ((one_le_div hW_pos).2 h_lower) (one_lt_pow₀ one_lt_two hn.ne')
  rw [pow_right_comm, le_div_iff₀ hW_pos] at hk_lower
  rw [pow_right_comm, div_lt_iff₀ hW_pos, pow_succ', mul_pow] at hk_upper
  have hH : 2 ^ k ≤ W :=
    le_of_pow_le_pow_left₀ hn.ne' hW_pos.le (by grw [← h_upper, ← hk_lower, ← hW, mul_one])
  have h_fit : (2 * l₀ s * 2 ^ k) ^ n ≤ 2 ^ s := by
    rify
    grw [mul_pow _ (2 ^ k), h_room, ← hk_lower, mul_comm]
  obtain ⟨T, h_class, h_card, h_sparse⟩ := P.exists_large_isSparse h_fit hL
  refine ⟨T, h_class, ?_, h_sparse⟩
  push_cast at h_card
  calc (towerDeg s : ℝ) = 3 * l₀ s * 2 ^ s := by simp [towerDeg_eq]
    _ ≤ 3 * l₀ s * (2 ^ n * (2 ^ k) ^ n * W) := by grw [hk_upper]
    _ = (2 ^ k) ^ n / (n * (2 ^ k) ^ 2) * (3 * l₀ s * n * 2 ^ n * W * (2 ^ k) ^ 2) := by field
    _ ≤ #T * (W ^ 3 * W * W ^ 2) := by gcongr
    _ = #T * W ^ 6 := by ring

/-- Pigeonhole in the class group: given `h + 1` pairs `(I i, J i)` of finite places with
`I i * J i` principal, `h` the class number, there are `i ≠ j` with `I i * J j` principal. -/
lemma exists_ne_isPrincipal_mul {K : Type*} [Field K] [NumberField K]
    {I J : Fin (classNumber K + 1) → FinPlace K}
    (h_principal : ∀ i : Fin (classNumber K + 1), ((I i).asIdeal * (J i).asIdeal).IsPrincipal) :
    ∃ i j : Fin (classNumber K + 1), i ≠ j ∧ ((I i).asIdeal * (J j).asIdeal).IsPrincipal := by
  -- two of the `I i` have the same class, and the class of `J j` is the inverse of that of `I j`
  let c (v : FinPlace K) : ClassGroup (𝓞 K) :=
    mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h_iff (v w : FinPlace K) : (v.asIdeal * w.asIdeal).IsPrincipal ↔ c v * c w = 1 := by
    simp only [c, ← map_mul, MulMemClass.mk_mul_mk, mk0_eq_one_iff]
  obtain ⟨i, j, hij, h_same : c (I i) = c (I j)⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (c ∘ I) (by simp [← classNumber.eq_1])
  exact ⟨i, j, hij, by simpa only [h_iff, h_same] using h_principal j⟩

/-- The conditions on each of the two primes `p₀`, `p₁` of admissible data, whose product
`M = p₀ p₁` is called the principal level: `p` is a prime `≡ 1` modulo `q₂² = P.q₂ s ^ 2` in
`[b ^ 10, b ^ 11]`, where `b = exp L`. -/
structure Parameters.IsPrincipalLevelPrime (P : Parameters) (s : ℕ) (L : ℝ) (p : ℕ) : Prop where
  /-- `p` is prime. -/
  prime : p.Prime
  /-- `p ≡ 1` modulo `q₂²`. -/
  modEq_one : p ≡ 1 [MOD P.q₂ s ^ 2]
  /-- `p` lies in `[b ^ 10, b ^ 11]`. -/
  mem_Icc : (p : ℝ) ∈ Set.Icc (exp L ^ 10) (exp L ^ 11)

/-- The product `M = p₀ p₁` of the two primes of the principal level lies in `[b ^ 20, b ^ 22]`,
where `b = exp L`. -/
lemma Parameters.IsPrincipalLevelPrime.mul_mem_Icc {P : Parameters} {s p₀ p₁ : ℕ} {L : ℝ}
    (hp₀ : P.IsPrincipalLevelPrime s L p₀) (hp₁ : P.IsPrincipalLevelPrime s L p₁) :
    ((p₀ * p₁ : ℕ) : ℝ) ∈ Set.Icc (exp L ^ 20) (exp L ^ 22) :=
  ⟨by grw [Nat.cast_mul, ← hp₀.mem_Icc.1, ← hp₁.mem_Icc.1, ← pow_add],
    by grw [Nat.cast_mul, hp₀.mem_Icc.2, hp₁.mem_Icc.2, ← pow_add]⟩

/-- The primes `p₀`, `p₁`. Let `0 < W` and `(2 h + 2) W ≤ L`, with `h` the class number of `K`.
If each window `[U, U + W]` with `10 L ≤ U ≤ 11 L` holds the logarithm of a prime `≡ 1` modulo
`q₂² = P.q₂ s ^ 2`, there are two distinct such primes `p₀`, `p₁` in `[b ^ 10, b ^ 11]`,
`b = exp L`, whose product is the norm `α ᾱ` of an integer `α` of `K`. -/
lemma Parameters.exists_prime_pair_norm (P : Parameters) (s : ℕ) {W L : ℝ} (hW : 0 < W)
    (h_classNumber_le : (2 * classNumber P.K + 2) * W ≤ L)
    (h_window : ∀ U ∈ Set.Icc (10 * L) (11 * L), ∃ p : ℕ,
      p.Prime ∧ p ≡ 1 [MOD P.q₂ s ^ 2] ∧ log p ∈ Set.Icc U (U + W)) :
    ∃ (p₀ p₁ : ℕ) (α : 𝓞 P.K),
      p₀ ≠ p₁ ∧
      P.IsPrincipalLevelPrime s L p₀ ∧
      P.IsPrincipalLevelPrime s L p₁ ∧
      α * star α = p₀ * p₁ := by
  -- one prime from each of the `h + 1` disjoint windows starting at `10 L + 2 i W`
  have h_shift (i : Fin (classNumber P.K + 1)) : 0 ≤ i * W ∧ 2 * i * W + W ≤ L :=
    ⟨by positivity, by nlinarith [(mod_cast i.is_le : (i : ℝ) ≤ classNumber P.K)]⟩
  have h_exists (i : Fin (classNumber P.K + 1)) : ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD P.q₂ s ^ 2] ∧
      log p ∈ Set.Icc (10 * L + 2 * i * W) (10 * L + 2 * i * W + W) :=
    h_window (10 * L + 2 * i * W) ⟨by linarith [h_shift i], by linarith [h_shift i]⟩
  choose p hp h_mod h_log using h_exists
  have h_level (i : Fin (classNumber P.K + 1)) : P.IsPrincipalLevelPrime s L (p i) := by
    have hp_pos : (0 : ℝ) < p i := mod_cast (hp i).pos
    refine ⟨hp i, h_mod i, ?_⟩
    simp only [Set.mem_Icc, ← exp_nat_mul, ← le_log_iff_exp_le hp_pos, ← log_le_iff_le_exp hp_pos,
      Nat.cast_ofNat]
    exact ⟨by linarith [h_shift i, (h_log i).1], by linarith [h_shift i, (h_log i).2]⟩
  have h_inj : p.Injective := .of_lt_imp_ne fun i j (hij : i.val + 1 ≤ j) h_eq ↦ by
    rify at hij
    have h_lower : 10 * L + 2 * j * W ≤ log (p i) := by simpa only [h_eq] using (h_log j).1
    nlinarith only [hW, (h_log i).2, h_lower, hij]
  -- each `p i` is `≡ 1` mod `q₁ d`, so it splits in `K` as `I i * J i`
  have h_split (i : Fin (classNumber P.K + 1)) : ∃ I J : FinPlace P.K,
      I.q = p i ∧ J.q = p i ∧ Ideal.span {↑(p i)} = I.asIdeal * J.asIdeal := by
    have : Fact (p i).Prime := ⟨hp i⟩
    obtain ⟨I, hI⟩ := FinPlace.exists_natCast_mem P.K (p i)
    have hI_norm : I.q = p i := by
      simp [q_eq_iff_chiK_ne_neg_one I hI,
        P.chiK_eq_one_of_modEq_one ((h_mod i).of_dvd (P.q₁_mul_d_dvd_q₂.pow two_ne_zero))]
    obtain ⟨J, -, ⟨-, h_inert : I.q = p i ^ 2⟩ | h_two⟩ := prime_inert_or_eq_mul I hI
    -- the inert case would give `p i = p i ^ 2`
    exacts [by nlinarith only [hI_norm, h_inert, (hp i).one_lt], ⟨I, J, h_two⟩]
  choose I J hI hJ hIJ using h_split
  -- pigeonhole: some `I i * J j` with `i ≠ j` is principal; a generator has norm `p i * p j`
  obtain ⟨i, j, hij : i ≠ j, α, hα : (I i).asIdeal * (J j).asIdeal = .span {α}⟩ :=
    exists_ne_isPrincipal_mul (I := I) (J := J) fun i ↦ ⟨p i, (hIJ i).symm⟩
  exact ⟨p i, p j, α, h_inj.ne hij, h_level i, h_level j,
    by simp [← absNorm_span_eq_mul_star, ← hα, hI, hJ]⟩

/-- A prime `N ≡ 1` modulo `4` is a sum `a ^ 2 + b ^ 2` of two squares (Fermat), hence the norm
`y ȳ` of `y = a + b i` in the CM field `E = P.E s`, which contains `i`. -/
lemma Parameters.exists_mul_star_eq_prime (P : Parameters) (s : ℕ) {N : ℕ} (hN : N.Prime)
    (h_mod : N ≡ 1 [MOD 4]) : ∃ y : 𝓞 (P.E s), y * star y = N := by
  have : Fact N.Prime := ⟨hN⟩
  obtain ⟨a, b, hab : a ^ 2 + b ^ 2 = N⟩ := Nat.Prime.sq_add_sq (h_mod.trans_ne (by norm_num))
  obtain ⟨i, hi_sq, hi_star⟩ : ∃ i : 𝓞 (P.E s), i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  refine ⟨a + b * i, ?_⟩
  simp only [← hab, star_add, star_mul, hi_star, star_natCast, Nat.cast_add, Nat.cast_pow]
  linear_combination -(b : 𝓞 (P.E s)) ^ 2 * hi_sq

/-- For `1 < q` and `1 < z`, the least power of `q` that is at least `z` is some `q ^ (e + 1)` with
`q ^ e < z`. -/
lemma exists_isLeast_pow {q : ℕ} {z : ℝ} (hq : 1 < q) (hz : 1 < z) :
    ∃ e : ℕ, IsLeast {n : ℕ | (∃ j : ℕ, n = q ^ j) ∧ z ≤ n} (q ^ (e + 1)) ∧ (q : ℝ) ^ e < z := by
  have h_exists : ∃ j : ℕ, z ≤ (q : ℝ) ^ j :=
    (pow_unbounded_of_one_lt z (mod_cast hq)).imp fun _ ↦ le_of_lt
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (n := Nat.find h_exists) (by simpa using hz)
  have h_le : z ≤ (q : ℝ) ^ (e + 1) := by simpa [he] using Nat.find_spec h_exists
  refine ⟨e, ⟨⟨⟨_, rfl⟩, mod_cast h_le⟩, ?_⟩, not_le.1 (Nat.find_min h_exists (by omega))⟩
  rintro _ ⟨⟨j, rfl⟩, hj⟩
  exact Nat.pow_le_pow_right hq.le (he.ge.trans (Nat.find_min' h_exists (mod_cast hj)))

/-- The ranks at `x = exp y`, `y ≥ 2`. The least power `m` of `2` with `m ≥ √x` is at most `2 √x`,
and the least power `r` of `3` with `r ≥ x⁵` is at most `3 x⁵`. Both have a positive exponent, and
for `m = 2 ^ (e + 1)` the exponent `s = 22 (e + 1)` is at most `32 log x`. -/
lemma exists_isLeast_two_pow_three_pow {y : ℝ} (hy : 2 ≤ y) :
    ∃ m r s : ℕ,
      IsLeast {n : ℕ | (∃ j : ℕ, n = 2 ^ j) ∧ exp (y / 2) ≤ n} m ∧
      IsLeast {n : ℕ | (∃ j : ℕ, n = 3 ^ j) ∧ exp (5 * y) ≤ n} r ∧
      m ≤ 2 * exp (y / 2) ∧
      r ≤ 3 * exp (5 * y) ∧
      (∃ e : ℕ, m = 2 ^ (e + 1) ∧ s = (e + 1) * 22) ∧
      (∃ e : ℕ, r = 3 ^ (e + 1)) ∧
      s ≤ 32 * y := by
  obtain ⟨a, hm, hm_pred_lt : ((2 : ℕ) : ℝ) ^ a < exp (y / 2)⟩ :=
    exists_isLeast_pow (z := exp (y / 2)) one_lt_two (by bound)
  obtain ⟨c, hr, hr_pred_lt : ((3 : ℕ) : ℝ) ^ c < exp (5 * y)⟩ :=
    exists_isLeast_pow (q := 3) (z := exp (5 * y)) (by simp) (by bound)
  refine ⟨2 ^ (a + 1), 3 ^ (c + 1), (a + 1) * 22, hm, hr, by simpa [pow_succ'] using hm_pred_lt.le,
    by simpa [pow_succ'] using hr_pred_lt.le, ⟨a, rfl, rfl⟩, ⟨c, rfl⟩, ?_⟩
  -- `a log 2 < y / 2` and `2 ≤ y`
  rw [← log_lt_iff_lt_exp (by positivity), log_pow, Nat.cast_ofNat] at hm_pred_lt
  push_cast
  nlinarith [log_two_gt_d9]

/-- The inequality `2 l₀ (k t + 1) < 2 ^ s` for `k = r + 1 - m`, `t = 5 r` and
`l₀ = 3 ^ (⌊log₃ s⌋ + 4)`, the bound on the exponents in `Parameters.IsSparse`. It holds when
`0 < y`, `10⁶ y ≤ exp y`, `exp (y / 2) ≤ m`, `r ≤ 3 exp (5 y)`, `2 ^ s = m ^ 22` and
`l₀ ≤ 2592 y`. -/
lemma mul_rank_lt_two_pow {y : ℝ} {m r s : ℕ} (hy : 0 < y) (h_large : 1e6 * y ≤ exp y)
    (hm : exp (y / 2) ≤ m) (hr : r ≤ 3 * exp (5 * y)) (h_pow : 2 ^ s = m ^ 22)
    (hl : l₀ s ≤ 2592 * y) : 2 * l₀ s * ((r + 1 - m) * (5 * r) + 1) < 2 ^ s := by
  have h_rank : (((r + 1 - m) * (5 * r) + 1 : ℕ) : ℝ) ≤ 46 * exp (5 * y) ^ 2 := by
    have hm_pos : 0 < m := mod_cast (exp_pos _).trans_le hm
    grw [show r + 1 - m ≤ r by omega]
    push_cast
    grw [hr, hr]
    linarith [one_le_pow₀ (n := 2) (one_le_exp (x := 5 * y) (by positivity))]
  rw [h_pow, ← Nat.cast_lt (α := ℝ), Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  calc _ ≤ 2 * (2592 * y) * (46 * exp (5 * y) ^ 2) := by grw [h_rank, hl, Nat.cast_ofNat]
    _ < 1e6 * y * exp (5 * y) ^ 2 := by nlinarith [mul_pos hy (pow_pos (exp_pos (5 * y)) 2)]
    _ ≤ exp y * exp (5 * y) ^ 2 := by gcongr
    _ = exp (y / 2) ^ 22 := by
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      ring_nf
    _ ≤ m ^ 22 := by gcongr

/-- The modulus `q₂² = P.q₂ s ^ 2` is at most `W ^ n` if `2 ≤ y`, `0 < W`, `s ≤ 32 y` and
`99 q₀ d y ≤ n log W`. -/
lemma Parameters.q₂_sq_le (P : Parameters) {s n : ℕ} {y W : ℝ} (hy : 2 ≤ y) (hW : 0 < W)
    (hs : s ≤ 32 * y) (hn : 99 * P.q₀ * P.d * y ≤ n * log W) : (P.q₂ s ^ 2 : ℕ) ≤ W ^ n := by
  have h_prod : (0 : ℝ) ≤ P.q₀ * P.d := by positivity
  rw [Parameters.q₂, ← pow_mul, Nat.cast_pow, Nat.cast_mul]
  refine pow_le_of_le_log hW ?_
  grw [log_pow, ← hn, log_le_self h_prod]
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_right hs h_prod, mul_le_mul_of_nonneg_right hy h_prod]

/-- For `0 ≤ W`, the logarithm of the integer `⌊exp W⌋` lies in `[W - 1, W]`. -/
lemma log_floor_exp_mem_Icc {W : ℝ} (hW : 0 ≤ W) : log ⌊exp W⌋₊ ∈ Set.Icc (W - 1) W := by
  have h_one : (1 : ℝ) ≤ ⌊exp W⌋₊ := mod_cast Nat.floor_pos.2 (one_le_exp hW)
  rw [Set.mem_Icc, le_log_iff_exp_le (by linarith), log_le_iff_le_exp (by linarith), exp_sub,
    div_le_iff₀ (exp_pos 1)]
  -- `exp W ≤ ⌊exp W⌋ e`, since `exp W < ⌊exp W⌋ + 1 ≤ 2 ⌊exp W⌋` and `2 ≤ e`
  exact ⟨by nlinarith [Nat.lt_floor_add_one (exp W), add_one_le_exp 1], Nat.floor_le (exp_pos W).le⟩

/-- The least multiple of `q` that exceeds `exp U` has logarithm in `[U, U + 1]` if `q ≤ exp U`. -/
lemma exists_isLeast_dvd_and_exp_lt {q : ℕ} {U : ℝ} (hq : 0 < q) (h_le : q ≤ exp U) :
    ∃ b : ℕ, IsLeast {b : ℕ | q ∣ b ∧ exp U < b} b ∧ log b ∈ Set.Icc U (U + 1) := by
  have hq' : (0 : ℝ) < q := mod_cast hq
  have h_lt_iff (c : ℕ) : exp U < (q * c : ℕ) ↔ ⌊exp U / q⌋₊ < c := by
    rw [Nat.floor_lt (by positivity), div_lt_iff₀' hq', Nat.cast_mul]
  have h_lt : exp U < (q * (⌊exp U / q⌋₊ + 1) : ℕ) := (h_lt_iff _).2 (Nat.lt_succ_self _)
  refine ⟨_, ⟨⟨dvd_mul_right .., h_lt⟩, ?_⟩, (le_log_iff_exp_le (by positivity)).2 h_lt.le, ?_⟩
  · rintro _ ⟨⟨c, rfl⟩, hc⟩
    exact Nat.mul_le_mul_left q ((h_lt_iff c).1 hc)
  · have h_floor : q * ⌊exp U / q⌋₊ ≤ exp U := (le_div_iff₀' hq').1 (Nat.floor_le (by positivity))
    rw [log_le_iff_le_exp (by positivity), exp_add, Nat.cast_mul, Nat.cast_succ]
    nlinarith [add_one_le_exp 1, exp_pos U]

/-- `W ^ n exp W ≤ exp (W ^ 6)` if `1 ≤ W` and `n + 1 ≤ W`. -/
lemma pow_mul_exp_le_exp_pow_six {n : ℕ} {W : ℝ} (hW : 1 ≤ W) (hn : n + 1 ≤ W) :
    W ^ n * exp W ≤ exp (W ^ 6) :=
  calc W ^ n * exp W ≤ exp W ^ n * exp W := by
        gcongr
        linarith [add_one_le_exp W]
    _ = exp ((n + 1) * W) := by rw [← exp_nat_mul, ← exp_add, add_one_mul]
    _ ≤ exp (W ^ 6) := by grw [hn, ← sq, pow_le_pow_right₀ hW (by norm_num : 2 ≤ 6)]

/-- The scale `b`, the least multiple of `q x₁` above `exp (W ^ 6)`, where `x₁ = ⌊exp W⌋` and
`q ≤ W ^ n`: `log b` lies in `[W ^ 6, W ^ 6 + 1]`, and `log log b` in `[6 log W, 6 log W + 1]`. -/
lemma exists_isLeast_dvd_log_log_mem_Icc {q n : ℕ} {W : ℝ} (hq : 0 < q) (hW : 1 ≤ W)
    (hn : n + 1 ≤ W) (hq_le : q ≤ W ^ n) :
    ∃ b : ℕ, IsLeast {b : ℕ | q * ⌊exp W⌋₊ ∣ b ∧ exp (W ^ 6) < b} b ∧
      log b ∈ Set.Icc (W ^ 6) (W ^ 6 + 1) ∧
      log (log b) ∈ Set.Icc (6 * log W) (6 * log W + 1) := by
  have hW_pow : 1 ≤ W ^ 6 := one_le_pow₀ hW
  have h_step_le : (q * ⌊exp W⌋₊ : ℕ) ≤ exp (W ^ 6) := by
    grw [← pow_mul_exp_le_exp_pow_six hW hn, Nat.cast_mul, hq_le, Nat.floor_le (exp_pos W).le]
  obtain ⟨b, hb, h_lower, h_upper⟩ := exists_isLeast_dvd_and_exp_lt
    (mul_pos hq (Nat.floor_pos.2 (one_le_exp (by linarith)))) h_step_le
  have h_log_pow : log (W ^ 6) = 6 * log W := by simp
  refine ⟨b, hb, ⟨h_lower, h_upper⟩, h_log_pow.ge.trans (log_le_log (by linarith) h_lower), ?_⟩
  rw [← h_log_pow, log_le_iff_le_exp (by linarith), exp_add, exp_log (by linarith)]
  nlinarith [add_one_le_exp 1]

/-- Let `2 ≤ y`, `0 < n`, `10⁶ y ≤ W ≤ exp (y / 2) ≤ m`, `r ≤ 3 exp (5 y)`,
`2 ^ s = m ^ 22 ≤ W ^ n`, `s ≤ 32 y`, `(5184 y) ^ n ≤ W` and `7776 y n 2 ^ n ≤ W`. At least
`towerDeg s / W ^ 6` places of class `-1` modulo `q₀` form a set that is sparse for the primes
`ℓ ≤ k t`, where `k = r + 1 - m` and `t = 5 r`: it has no places `σ, τ, ρ` with `τ / σ ≡ ± ℓ ^ i`
and `ρ / σ ≡ ± ℓ ^ j`, `0 < i < j < l₀`, modulo the part of `q₁` prime to `ℓ`
(`Parameters.IsSparse`). -/
lemma Parameters.exists_isSparse_of_ranks (P : Parameters) {m r s n : ℕ} {y W : ℝ} (hy : 2 ≤ y)
    (hn : 0 < n) (hm : exp (y / 2) ≤ m) (hr : r ≤ 3 * exp (5 * y)) (h_pow : 2 ^ s = m ^ 22)
    (hs : s ≤ 32 * y) (hW : W ≤ exp (y / 2)) (h_upper : 2 ^ s ≤ W ^ n) (h_large : 1e6 * y ≤ W)
    (h_room : (5184 * y) ^ n ≤ W) (h_count : 7776 * y * n * 2 ^ n ≤ W) :
    ∃ T : Finset (P.Φ s), (∀ σ ∈ T, P.placeClass (P.q₀.dvd_mul_right (towerDeg s)) σ = -1) ∧
      towerDeg s ≤ #T * W ^ 6 ∧
      P.IsSparse s ((r + 1 - m) * (5 * r)) T := by
  have hW_one : 1 < W := by linarith
  have h_lower : W ≤ 2 ^ s :=
    calc W ≤ m ^ 22 := (hW.trans hm).trans (le_self_pow₀ (by linarith) (by norm_num))
      _ = 2 ^ s := mod_cast h_pow.symm
  have hs_ne : s ≠ 0 := fun h ↦ by simp [h, hW_one.not_ge] at h_lower
  have hl : l₀ s ≤ 2592 * y := by linarith [show (l₀ s : ℝ) ≤ 81 * s from mod_cast l₀_le_mul hs_ne]
  have h_exp : 1e6 * y ≤ exp y := (h_large.trans hW).trans (exp_le_exp.2 (by linarith))
  refine P.exists_isSparse hn hW_one.le h_lower h_upper ?_ ?_
    (mul_rank_lt_two_pow (by linarith) h_exp hm hr h_pow hl)
  · grw [← h_room, hl, ← mul_assoc, show (2 * 2592 : ℝ) = 5184 by norm_num]
  · grw [hl, ← le_self_pow₀ hW_one.le three_ne_zero]
    linarith

/-- The level `N`. Let `E = P.E s = K(ζ_{q₁})` with `K = ℚ(√-d)`, `d = P.d` and `q₁ = P.q₁ s`. Let
`b = exp L` with `7 ≤ L` and `W ^ 2 ≤ L`, let `2 ≤ m`, let the weights `κ τ` at the infinite places
`τ` of `E` lie in `[1, b]` and `M` in `[b ^ 20, b ^ 22]`, and let `q₁ d ≤ b`. Let each window
`[U, U + W]` with `m L ≤ U ≤ 24 m L` hold the logarithm of a prime `≡ 1` modulo `q₂²`. There is such
a prime `N` with `log N₋ ≤ log N ≤ log N₋ + √L` and `N = y ȳ` for an integer `y` of `E`. -/
lemma Parameters.exists_prime_log_mem_Icc_mul_star_eq (P : Parameters) {s m M : ℕ} {κ : P.Φ s → ℕ}
    {W L : ℝ} (hm_two : 2 ≤ m) (hL_seven : 7 ≤ L) (hW_sq : W ^ 2 ≤ L)
    (hκ_mem : ∀ τ : P.Φ s, (κ τ : ℝ) ∈ Set.Icc 1 (exp L))
    (hM_mem : (M : ℝ) ∈ Set.Icc (exp L ^ 20) (exp L ^ 22)) (h_cond : (P.q₁ s * P.d : ℕ) ≤ exp L)
    (h_window : ∀ U ∈ Set.Icc (m * L) (24 * m * L), ∃ p : ℕ,
      p.Prime ∧ p ≡ 1 [MOD P.q₂ s ^ 2] ∧ log p ∈ Set.Icc U (U + W)) :
    ∃ (N : ℕ) (y : 𝓞 (P.E s)), N.Prime ∧ N ≡ 1 [MOD P.q₂ s ^ 2] ∧
      log N ∈ Set.Icc (P.logLevelMin s m κ M L) (P.logLevelMin s m κ M L + √L) ∧
      y * star y = N := by
  obtain ⟨N, hN, h_mod, h_lower, h_upper⟩ :=
    h_window _ (P.logLevelMin_mem_Icc hm_two hL_seven hκ_mem hM_mem h_cond)
  have h_four : 4 ∣ P.q₂ s ^ 2 :=
    calc 4 ∣ P.q₀ := .trans (by norm_num) P.dvd_q₀
      _ ∣ P.q₁ s * P.d := (dvd_mul_right P.q₀ (towerDeg s)).mul_right P.d
      _ ∣ P.q₂ s ^ 2 := P.q₁_mul_d_dvd_q₂.pow two_ne_zero
  obtain ⟨y, hy⟩ := P.exists_mul_star_eq_prime s hN (h_mod.of_dvd h_four)
  exact ⟨N, y, hN, h_mod, ⟨h_lower, by grw [h_upper, le_sqrt_of_sq_le hW_sq]⟩, hy⟩

/-- For any proposition `p`, the value `if p then b else x * b / x₁` (natural-number division) lies
in `[1, b]` if `1 ≤ x ≤ x₁ ≤ b`. -/
lemma ite_mul_div_mem_Icc {x x₁ b : ℕ} (hx : 1 ≤ x) (hx₁ : x ≤ x₁) (hb : x₁ ≤ b) (p : Prop)
    [Decidable p] : (if p then b else x * b / x₁) ∈ Set.Icc 1 b := by
  split_ifs
  exacts [⟨by omega, le_rfl⟩, ⟨Nat.div_pos (hb.trans (Nat.le_mul_of_pos_left b hx)) (by omega),
    Nat.div_le_of_le_mul (Nat.mul_le_mul_right b hx₁)⟩]

lemma exp_five_mul_log {x : ℝ} (hx : 0 < x) : exp (5 * log x) = x ^ 5 := by
  simpa [exp_log hx] using exp_nat_mul (log x) 5

lemma rpow_div_six_pow_six (x : ℕ) (ε : ℝ) : ((x : ℝ) ^ (ε / 6)) ^ 6 = (x : ℝ) ^ ε := by
  simp [← rpow_mul_natCast x.cast_nonneg]

/-! ### Admissible data -/

/-- The admissible data at the integer `x` and the real `W`. The ranks `m`, `r`, the exponent `s`
and the scales `x₁ = ⌊exp W⌋` and `b` are determined by `x` and `W`; the set `T` of `b`-places (the
infinite places of `P.E s` that get the weight `b`), the
primes `p₀ = g 0`, `p₁ = g 1`, `N` and the elements `α`, `β` with `α ᾱ = p₀ p₁` and `β β̄ = N` are
any with the listed properties. -/
structure Parameters.IsAdmissibleData (P : Parameters) (x : ℕ) (W : ℝ) (m r s b : ℕ)
    (T : Finset (P.Φ s)) (g : Fin 2 → ℕ) (α : 𝓞 P.K) (N : ℕ) (β : 𝓞 (P.E s)) : Prop where
  /-- `m` is the least power of `2` with `m ≥ √x`. -/
  isLeast_m : IsLeast {n : ℕ | (∃ j : ℕ, n = 2 ^ j) ∧ √x ≤ n} m
  /-- `r` is the least power of `3` with `r ≥ x⁵`. -/
  isLeast_r : IsLeast {n : ℕ | (∃ j : ℕ, n = 3 ^ j) ∧ (x : ℝ) ^ 5 ≤ n} r
  /-- `s = 22 log₂ m`. -/
  two_pow_eq : 2 ^ s = m ^ 22
  /-- `b` is the least multiple of `q₁ x₁` that exceeds `exp (W ^ 6)`. -/
  isLeast_b : IsLeast {c : ℕ | P.q₁ s * ⌊exp W⌋₊ ∣ c ∧ exp (W ^ 6) < c} b
  /-- The `b`-places are `≡ -1` modulo `q₀`. -/
  placeClass_eq_neg_one : ∀ σ ∈ T, P.placeClass (P.q₀.dvd_mul_right (towerDeg s)) σ = -1
  /-- There are at least `towerDeg s / log b` of them. -/
  towerDeg_le : towerDeg s ≤ #T * log b
  /-- The `b`-places are sparse for the primes up to `k t`, where `k = r + 1 - m` and `t = 5 r`. -/
  sparse : P.IsSparse s ((r + 1 - m) * (5 * r)) T
  /-- `p₀` and `p₁` are prime. -/
  levelPrime_prime (i : Fin 2) : (g i).Prime
  /-- `p₀, p₁ ≡ 1` modulo `q₂²`. -/
  levelPrime_modEq_one (i : Fin 2) : g i ≡ 1 [MOD P.q₂ s ^ 2]
  /-- `p₀ ≠ p₁`. -/
  levelPrime_injective : g.Injective
  /-- `p₀` and `p₁` lie in `[b¹⁰, b¹¹]`. -/
  levelPrime_mem (i : Fin 2) : (g i : ℝ) ∈ Set.Icc ((b : ℝ) ^ 10) ((b : ℝ) ^ 11)
  /-- The norm of `α` is `p₀ p₁`. -/
  α_mul_star : α * star α = g 0 * g 1
  /-- The level `N` is prime. -/
  N_prime : N.Prime
  /-- `N ≡ 1` modulo `q₂²`. -/
  N_modEq_one : N ≡ 1 [MOD P.q₂ s ^ 2]
  /-- `log N₋ ≤ log N ≤ log N₋ + √(log b)`, for the weights `b` on `T` and `x b / x₁` elsewhere. -/
  log_N_mem :
    let κ (τ : P.Φ s) : ℕ := if τ ∈ T then b else x * b / ⌊exp W⌋₊
    log N ∈ Set.Icc (P.logLevelMin s m κ (g 0 * g 1) (log b))
      (P.logLevelMin s m κ (g 0 * g 1) (log b) + √(log b))
  /-- `β` times its complex conjugate is `N`. -/
  β_mul_star : β * star β = N

/-- The fields of the admissible data `D` are the given values, with `x₁ = ⌊exp W⌋`. The arguments
are those of `Parameters.IsAdmissibleData`. The heterogeneous equality `≍` is used where the type of
a field depends on `D.towerExp`. -/
structure Data.HasFields {P : Parameters} (D : Data P) (x : ℕ) (W : ℝ) (m r s b : ℕ)
    (T : Finset (P.Φ s)) (g : Fin 2 → ℕ) (α : 𝓞 P.K) (N : ℕ) (β : 𝓞 (P.E s)) : Prop where
  /-- The length of the prime sum is `x`. -/
  natX_eq : D.natX = x
  /-- The scale `x₁` is `⌊exp W⌋`. -/
  natX₁_eq : D.natX₁ = ⌊exp W⌋₊
  /-- The scale `D.natB` is `b`. -/
  natB_eq : D.natB = b
  /-- The rank `D.m` is `m`. -/
  m_eq : D.m = m
  /-- The rank `D.r` is `r`. -/
  r_eq : D.r = r
  /-- The exponent of the tower is `s`. -/
  towerExp_eq : D.towerExp = s
  /-- The set of `b`-places is `T`. -/
  bPlaces_heq : D.bPlaces ≍ T
  /-- The primes `p₀`, `p₁` are `g 0`, `g 1`. -/
  levelPrime_eq : D.levelPrime = g
  /-- The integer of `K` of norm `p₀ p₁` is `α`. -/
  piMBar_eq : D.piMBar = α
  /-- The level is `N`. -/
  N_eq : D.N = N
  /-- The integer of `E` whose product with its conjugate is the level is `β`. -/
  piN_heq : D.piN ≍ β

/-- `W` is a large scale for `y` with exponent `n`: `W` is small against `x = exp y` and large
against the parameters, `n` and the multiples of `y` and `y ^ n` listed below; `n` is so large that
`q₂² ≤ W ^ n` for `s ≤ 32 y` (`Parameters.q₂_sq_le`). -/
structure Parameters.IsLargeScale (P : Parameters) (n : ℕ) (y W : ℝ) : Prop where
  /-- `(e W ^ 6) ^ 100 ≤ x`. -/
  log_W_le : 100 * (6 * log W + 1) ≤ y
  /-- `log W` is large against `P.constantBound`, a bound for the constants that depend on `q₀` and
  `d` only. -/
  const_le : 1e12 * P.constantBound ≤ log W
  /-- `W` is large against `y`. -/
  mul_y_le_W : 2e6 * y ≤ W
  /-- `W` is large against the class number of `K`. -/
  classNumber_le : 2 * classNumber P.K + 2 ≤ W
  /-- `n` is positive. -/
  n_pos : 0 < n
  /-- `n` is small against `W`. -/
  add_one_le : n + 1 ≤ W
  /-- `n log W` is large against `log q₂²`. -/
  le_mul_log_W : 99 * P.q₀ * P.d * y ≤ n * log W
  /-- Room for a set of Behrend's type. -/
  pow_le : (5184 * y) ^ n ≤ W
  /-- The loss in the size of that set. -/
  mul_two_pow_le : 7776 * y * n * 2 ^ n ≤ W

/-- For `0 < ε < 1 / 100` there is an `n` such that `W = x ^ (ε / 6)` is a large scale for
`y = log x` with exponent `n` at every large integer `x`: `0 < n`, `100 (6 log W + 1) ≤ y`,
`99 q₀ d y ≤ n log W`, and `W` is at least `2 · 10⁶ y`, `(5184 y) ^ n`, `7776 y n 2 ^ n`, `n + 1`,
`2 h + 2` with `h` the class number of `K = P.K`, and `exp (10¹² c)`, where `c = P.constantBound`
bounds the constants that depend on `q₀ = P.q₀` and `d = P.d` only. -/
lemma Parameters.exists_eventually_isLargeScale (P : Parameters) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < 1 / 100) :
    ∃ n : ℕ, ∀ᶠ x : ℕ in atTop, P.IsLargeScale n (log x) ((x : ℝ) ^ (ε / 6)) := by
  have hε_six : 0 < ε / 6 := by positivity
  obtain ⟨n, hn, hn_pos⟩ : ∃ n : ℕ, 99 * P.q₀ * P.d < n * (ε / 6) ∧ 0 < n := by
    simpa [div_lt_iff₀ hε_six] using exists_nat_gt (99 * P.q₀ * P.d / (ε / 6) ⊔ 0)
  have hW : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (ε / 6)) atTop atTop :=
    (tendsto_rpow_atTop hε_six).comp tendsto_natCast_atTop_atTop
  have h_pow_le (c : ℝ) (j : ℕ) : ∀ᶠ x : ℕ in atTop, c * log x ^ j ≤ (x : ℝ) ^ (ε / 6) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_rpow_atTop j hε_six).const_mul_left c).eventuallyLE] with x hx
    simpa [abs_of_nonneg (rpow_nonneg x.cast_nonneg _)] using (le_norm_self _).trans hx
  use n
  filter_upwards [eventually_gt_atTop 0, h_pow_le 2e6 1, h_pow_le (5184 ^ n) n,
    h_pow_le (7776 * n * 2 ^ n) 1, hW.eventually_ge_atTop (exp (1e12 * P.constantBound)),
    hW.eventually_ge_atTop (2 * classNumber P.K + 2), hW.eventually_ge_atTop (n + 1),
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (100 / (1 - 100 * ε))]
    with x hx h_large h_room h_count h_const h_classNumber hn_le
      (h_small : 100 / (1 - 100 * ε) ≤ log x)
  have h_log : log ((x : ℝ) ^ (ε / 6)) = ε / 6 * log x := log_rpow (mod_cast hx) _
  exact
    { log_W_le := by linarith only [h_log, (div_le_iff₀ (by linarith)).1 h_small]
      const_le := (le_log_iff_exp_le (by positivity)).2 h_const
      mul_y_le_W := by simpa only [pow_one] using h_large
      classNumber_le := h_classNumber, n_pos := hn_pos, add_one_le := hn_le
      le_mul_log_W := by grw [h_log, hn, mul_assoc]
      pow_le := by rwa [mul_pow]
      mul_two_pow_le := by linarith only [h_count] }

namespace Parameters.IsLargeScale

variable {P : Parameters} {n s : ℕ} {y W : ℝ}

/-- A large scale `W` (`Parameters.IsLargeScale`) is at least `1`. -/
lemma one_le (h_scale : P.IsLargeScale n y W) : 1 ≤ W := by
  linarith [h_scale.add_one_le, n.cast_nonneg (α := ℝ)]

/-- If `W` is a large scale for `y` (`Parameters.IsLargeScale`), then `100 ≤ y`. -/
lemma hundred_le (h_scale : P.IsLargeScale n y W) : 100 ≤ y := by
  linarith [h_scale.log_W_le, log_nonneg h_scale.one_le]

/-- At a large scale `W`, the modulus `q₂² = P.q₂ s ^ 2` is at most `W ^ n` for `s ≤ 32 y`. -/
lemma q₂_sq_le (h_scale : P.IsLargeScale n y W) (hs : s ≤ 32 * y) : (P.q₂ s ^ 2 : ℕ) ≤ W ^ n :=
  P.q₂_sq_le (by linarith [h_scale.hundred_le]) (one_pos.trans_le h_scale.one_le) hs
    h_scale.le_mul_log_W

/-- At a large scale `W`, `q₁ d ≤ W ^ n` for `s ≤ 32 y`, as `q₁ d` divides `q₂²`. -/
lemma q₁_mul_d_le (h_scale : P.IsLargeScale n y W) (hs : s ≤ 32 * y) :
    (P.q₁ s * P.d : ℕ) ≤ W ^ n := by
  grw [Nat.le_of_dvd (NeZero.pos _) (P.q₁_mul_d_dvd_q₂.pow two_ne_zero), h_scale.q₂_sq_le hs]

/-- At a large scale `W`, `2 ^ s ≤ W ^ n` for `s ≤ 32 y`, as `2 ^ s` divides `q₁ d`. -/
lemma two_pow_le (h_scale : P.IsLargeScale n y W) (hs : s ≤ 32 * y) : 2 ^ s ≤ W ^ n :=
  (h_scale.q₁_mul_d_le hs).trans' <| mod_cast Nat.le_of_dvd (mul_pos (NeZero.pos _) P.d_prime.pos)
    (((pow_dvd_pow 2 s.le_succ).trans P.two_pow_dvd_q₁).mul_right P.d)

/-- Let `W` be a large scale for `y` with exponent `n` under the parameters `P`
(`Parameters.IsLargeScale`). If `s ≤ 32 y` and `W ^ 6 ≤ L`, then `P.q₁ s * P.d ≤ exp L`. -/
lemma q₁_mul_d_le_exp (h_scale : P.IsLargeScale n y W) (hs : s ≤ 32 * y) {L : ℝ} (hL : W ^ 6 ≤ L) :
    (P.q₁ s * P.d : ℕ) ≤ exp L := by
  have hW : 0 ≤ W := zero_le_one.trans h_scale.one_le
  grw [h_scale.q₁_mul_d_le hs, ← hL,
    ← pow_mul_exp_le_exp_pow_six h_scale.one_le h_scale.add_one_le, ← one_le_exp hW, mul_one]

/-- Let the real `W` be a large scale for the real `y`, and let `s` be a natural number with
`s ≤ 32 y`. The least multiple `b` of `P.q₁ s * ⌊exp W⌋` above `exp (W ^ 6)` is positive, in the
form `exp (log b) = b`; it has `log b` in `[W ^ 6, W ^ 6 + 1]` and `log log b` in
`[6 log W, 6 log W + 1]`. -/
lemma exists_isLeast_dvd_log_log_mem_Icc (h_scale : P.IsLargeScale n y W) (hs : s ≤ 32 * y) :
    ∃ b : ℕ, IsLeast {c : ℕ | P.q₁ s * ⌊exp W⌋₊ ∣ c ∧ exp (W ^ 6) < c} b ∧
      exp (log b) = b ∧
      log b ∈ Set.Icc (W ^ 6) (W ^ 6 + 1) ∧
      log (log b) ∈ Set.Icc (6 * log W) (6 * log W + 1) := by
  have hq₁_le : P.q₁ s ≤ W ^ n := by
    grw [Nat.le_mul_of_pos_right (P.q₁ s) P.d_prime.pos, h_scale.q₁_mul_d_le hs]
  obtain ⟨b, ⟨⟨hb_dvd, hb_lt⟩, hb_min⟩, h_log⟩ :=
    New.exists_isLeast_dvd_log_log_mem_Icc (NeZero.pos (P.q₁ s)) h_scale.one_le h_scale.add_one_le
      hq₁_le
  exact ⟨b, ⟨⟨hb_dvd, hb_lt⟩, hb_min⟩, exp_log ((exp_pos (W ^ 6)).trans hb_lt), h_log⟩

end Parameters.IsLargeScale

/-- Let `W` be a large scale for `log x`, and let admissible data at `x` and `W` be given. A term
`D : Data P` bundles such objects and scales `x`, `x₁` with the inequalities `(log b) ^ 100 ≤ x`,
`x ^ 10⁶ ≤ x₁`, `x₁ ^ 10⁶ ≤ b`, `(log x₁) ^ 6 ≤ log b`, `10¹² P.constantBound ≤ log log b`,
`m ∈ [√x, 2 √x]` and `r ∈ [x⁵, 3 x⁵]`. There is a `D` whose fields equal the given objects, with
`x₁ = ⌊exp W⌋` (`Data.HasFields`). Moreover `W - 1 ≤ log x₁` and `W ^ 6 ≤ log b ≤ W ^ 6 + 1`. -/
lemma Parameters.IsAdmissibleData.exists_hasFields {P : Parameters} {x n m r s b N : ℕ} {W : ℝ}
    {T : Finset (P.Φ s)} {g : Fin 2 → ℕ} {α : 𝓞 P.K} {β : 𝓞 (P.E s)}
    (h_adm : P.IsAdmissibleData x W m r s b T g α N β) (h_scale : P.IsLargeScale n (log x) W) :
    ∃ D : Data P,
      D.HasFields x W m r s b T g α N β ∧
      W - 1 ≤ D.logX₁ ∧
      D.logB ∈ Set.Icc (W ^ 6) (W ^ 6 + 1) := by
  have hW_one : 1 ≤ W := h_scale.one_le
  have hy : 100 ≤ log x := h_scale.hundred_le
  have hx_pos : (0 : ℝ) < x := by linarith [log_le_self x.cast_nonneg]
  -- The ranks are those of `exists_isLeast_two_pow_three_pow`, and `b` is that of
  -- `exists_isLeast_dvd_log_log_mem_Icc`.
  obtain ⟨m', r', s', hm, hr, hm_upper, hr_upper, ⟨e, hm_pow, hs_eq⟩, hr_pow, hs⟩ :=
    exists_isLeast_two_pow_three_pow (y := log x) (by linarith)
  obtain rfl : m = m' := h_adm.isLeast_m.unique (by simpa [exp_half, exp_log hx_pos] using hm)
  obtain rfl : r = r' := h_adm.isLeast_r.unique (by simpa [exp_five_mul_log hx_pos] using hr)
  obtain rfl : s = s' := Nat.pow_right_injective le_rfl <|
    show 2 ^ s = 2 ^ s' by rw [h_adm.two_pow_eq, hs_eq, pow_mul, ← hm_pow]
  obtain ⟨b', hb, hb_eq, h_log_b, h_log_log_lower, h_log_log_upper⟩ :=
    h_scale.exists_isLeast_dvd_log_log_mem_Icc hs
  obtain rfl : b = b' := h_adm.isLeast_b.unique hb
  obtain ⟨⟨-, hm_lower : exp (log x / 2) ≤ m⟩, -⟩ := hm
  obtain ⟨⟨-, hr_lower : exp (5 * log x) ≤ r⟩, -⟩ := hr
  obtain ⟨⟨hb_dvd : P.q₁ s * ⌊exp W⌋₊ ∣ b, -⟩, -⟩ := hb
  obtain ⟨hx₁_lower : W - 1 ≤ log ⌊exp W⌋₊, hx₁_upper : log ⌊exp W⌋₊ ≤ W⟩ :=
    log_floor_exp_mem_Icc (zero_le_one.trans hW_one)
  have hb_large : 2e8 * W ≤ log b := by
    nlinarith only [pow_le_pow_right₀ hW_one (by norm_num : 2 ≤ 6), h_log_b.1, h_scale.mul_y_le_W,
      hy]
  have h_log_log : log (log ⌊exp W⌋₊) ≤ log W :=
    log_le_log (by linarith [h_scale.mul_y_le_W]) hx₁_upper
  -- the fields not listed are the fields of `h_adm` of the same name
  let D : Data P :=
    { h_adm with
      m, r, towerExp := s, levelPrime := g, N
      natX := x, natX₁ := ⌊exp W⌋₊, natB := b
      logX := log x, logX₁ := log ⌊exp W⌋₊, logB := log b
      bPlaces := T, piMBar := α, piN := β
      levelPrime_prime := h_adm.levelPrime_prime
      levelPrime_modEq_one_q₂_sq := h_adm.levelPrime_modEq_one
      levelPrime_injective := h_adm.levelPrime_injective
      N_modEq_one_q₂_sq := h_adm.N_modEq_one
      weight τ := if τ ∈ T then b else x * b / ⌊exp W⌋₊
      exp_logX := exp_log hx_pos
      exp_logX₁ := exp_log (mod_cast Nat.floor_pos.2 (one_le_exp (by linarith)))
      exp_logB := hb_eq
      constantBound_le := by linarith [h_scale.const_le, log_nonneg hW_one]
      mul_log_logB_le_logX := by linarith [h_scale.log_W_le]
      logX_le_logX₁ := by linarith [h_scale.mul_y_le_W]
      logX₁_le_logB := by linarith
      log_logX₁_le_log_logB := by linarith
      m_mem := ⟨hm_lower, hm_upper⟩, r_mem := ⟨hr_lower, hr_upper⟩
      exists_m_eq_two_pow := ⟨e, hm_pow, hs_eq⟩, exists_r_eq_three_pow := hr_pow
      towerExp_le := hs, dvd_natB := hb_dvd, weight_eq _ := rfl
      placeClass_of_mem_bPlaces := h_adm.placeClass_eq_neg_one
      towerDeg_le_card_bPlaces_mul := h_adm.towerDeg_le
      levelPrime_mem i := by simpa only [hb_eq] using h_adm.levelPrime_mem i
      piMBar_mul_star := h_adm.α_mul_star, piN_mul_star := h_adm.β_mul_star }
  have h_fields : D.HasFields x W m r s b T g α N β :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, .rfl, rfl, rfl, rfl, .rfl⟩
  exact ⟨D, h_fields, hx₁_lower, h_log_b⟩

/-- **Admissible data are fields of the data.** Let `0 < ε < 1 / 100`. For every large enough
integer `x`, any admissible data (`Parameters.IsAdmissibleData`) at `x` and `W = x ^ (ε / 6)` are
the fields of some `D : Data P` (`Data.HasFields`). This `D` has `x ^ (ε / 6) - 1 ≤ D.logX₁`, and
`D.logB` lies in `[x ^ ε, x ^ ε + 1]`. -/
theorem eventually_exists_data_of_isAdmissibleData (P : Parameters) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ (m r s b : ℕ) (T : Finset (P.Φ s)) (g : Fin 2 → ℕ) (α : 𝓞 P.K) (N : ℕ)
      (β : 𝓞 (P.E s)), P.IsAdmissibleData x ((x : ℝ) ^ (ε / 6)) m r s b T g α N β →
      ∃ D : Data P,
        D.HasFields x ((x : ℝ) ^ (ε / 6)) m r s b T g α N β ∧
        (x : ℝ) ^ (ε / 6) - 1 ≤ D.logX₁ ∧
        D.logB ∈ Set.Icc ((x : ℝ) ^ ε) ((x : ℝ) ^ ε + 1) := by
  obtain ⟨n, h_scale⟩ := P.exists_eventually_isLargeScale hε hε_lt
  filter_upwards [h_scale] with x hx m r s b T g α N β h_adm
  simpa only [rpow_div_six_pow_six] using h_adm.exists_hasFields hx

/-- Let `W` be a large scale for `y = log x` with exponent `n`. Let the windows `[U, U + W]` with
`W ≤ U ≤ W ^ (n + 7)` hold logarithms of primes `≡ 1` modulo the powers `(q₀ d) ^ k ≤ W ^ (n + 7)`,
`k > 1`. Then admissible data exist at `x` and `W`: the least powers `m ≥ √x` of `2` and `r ≥ x⁵` of
`3`; `s` with `2 ^ s = m ^ 22`; the least multiple `b > exp (W ^ 6)` of `P.q₁ s * ⌊exp W⌋`; a sparse
set `T` of at least `towerDeg s / log b` infinite places of `E = P.E s` of class `-1` modulo `q₀`;
distinct primes `g 0`, `g 1` in `[b¹⁰, b¹¹]` and a prime `N` with `log N` in the interval of length
`√(log b)` that starts at `P.logLevelMin`, all `≡ 1` modulo `(q₀ d) ^ (2 (s + 6))`; and integers `α`
of `K = P.K = ℚ(√-d)` and `β` of `E` with `α ᾱ = g 0 * g 1` and `β β̄ = N`. -/
lemma Parameters.IsLargeScale.exists_isAdmissibleData {P : Parameters} {x n : ℕ} {W : ℝ}
    (h_scale : P.IsLargeScale n (log x) W)
    (h_window : ∀ k : ℕ, 1 < k → ((P.q₀ * P.d : ℕ) : ℝ) ^ k ≤ W ^ (n + 7) →
      ∀ U ∈ Set.Icc W (W ^ (n + 7)), ∃ p : ℕ,
        p.Prime ∧ p ≡ 1 [MOD (P.q₀ * P.d) ^ k] ∧ log p ∈ Set.Icc U (U + W)) :
    ∃ (m r s b : ℕ) (T : Finset (P.Φ s)) (g : Fin 2 → ℕ) (α : 𝓞 P.K) (N : ℕ) (β : 𝓞 (P.E s)),
      P.IsAdmissibleData x W m r s b T g α N β := by
  have hW_one : 1 ≤ W := h_scale.one_le
  have hW_pos : 0 < W := by linarith
  have hy : 100 ≤ log x := h_scale.hundred_le
  have h_large : 2e6 * log x ≤ W := h_scale.mul_y_le_W
  have hx_pos : (0 : ℝ) < x := by linarith [log_le_self x.cast_nonneg]
  have hW_le : W ≤ exp (log x / 2) :=
    (log_le_iff_le_exp hW_pos).1 (by linarith [log_nonneg hW_one, h_scale.log_W_le])
  -- ranks and field; `W ≤ m ≤ 2 ^ s ≤ W ^ n` and `q₂ s ^ 2 ≤ W ^ n`
  obtain ⟨m, r, s, hm, hr, -, hr_upper, ⟨e, hm_pow, hs_eq⟩, -, hs⟩ :=
    exists_isLeast_two_pow_three_pow (y := log x) (by linarith)
  have h_pow : 2 ^ s = m ^ 22 := by rw [hm_pow, hs_eq, pow_mul]
  have h_two_pow : 2 ^ s ≤ W ^ n := h_scale.two_pow_le hs
  have hm_le : m ≤ W ^ n :=
    h_two_pow.trans' (mod_cast (Nat.le_self_pow (by norm_num) m).trans h_pow.ge)
  have hm_lower : exp (log x / 2) ≤ m := hm.1.2
  -- places
  obtain ⟨T, h_class_T, h_card, h_sparse⟩ := P.exists_isSparse_of_ranks (by linarith) h_scale.n_pos
    hm_lower hr_upper h_pow hs hW_le h_two_pow (by linarith) h_scale.pow_le h_scale.mul_two_pow_le
  -- scales and weights
  obtain ⟨b, hb, hb_eq, hL, -⟩ := h_scale.exists_isLeast_dvd_log_log_mem_Icc hs
  set L : ℝ := log b
  have hL_sq : W ^ 2 ≤ L := (pow_le_pow_right₀ hW_one (by norm_num)).trans hL.1
  have hL_large : 2e8 * W ≤ L := by nlinarith only [hL_sq, h_large, hy]
  have hm_mul : L ≤ m * L := le_mul_of_one_le_left (by linarith) (by linarith)
  have hx_le : x ≤ ⌊exp W⌋₊ := Nat.le_floor ((log_le_iff_le_exp hx_pos).1 (by linarith))
  have hb_ge : ⌊exp W⌋₊ ≤ b :=
    Nat.le_of_dvd (mod_cast (exp_pos L).trans_eq hb_eq) (dvd_of_mul_left_dvd hb.1.1)
  let κ (τ : P.Φ s) : ℕ := if τ ∈ T then b else x * b / ⌊exp W⌋₊
  have hκ (τ : P.Φ s) : (κ τ : ℝ) ∈ Set.Icc 1 (exp L) := by
    simpa [hb_eq] using ite_mul_div_mem_Icc (mod_cast hx_pos) hx_le hb_ge (τ ∈ T)
  -- primes and level, from windows that start in `[L, 24 m L] ⊆ [W, W ^ (n + 7)]`
  replace h_window (U : ℝ) (h_lower : L ≤ U) (h_upper : U ≤ 24 * m * L) :
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD P.q₂ s ^ 2] ∧ log p ∈ Set.Icc U (U + W) := by
    have h_top : 24 * L ≤ W ^ 7 := by
      nlinarith only [hL.2, one_le_pow₀ (n := 6) hW_one, h_large, hy]
    have h_modulus : (P.q₂ s ^ 2 : ℕ) ≤ W ^ (n + 7) :=
      (h_scale.q₂_sq_le hs).trans (pow_le_pow_right₀ hW_one (n.le_add_right 7))
    rw [Parameters.q₂, ← pow_mul] at h_modulus ⊢
    refine h_window _ (by omega) (mod_cast h_modulus) U ⟨by linarith, ?_⟩
    calc U ≤ m * (24 * L) := by linarith
      _ ≤ W ^ (n + 7) := by grw [hm_le, h_top, pow_add]
  have h_classNumber_le : (2 * classNumber P.K + 2) * W ≤ L := by
    grw [h_scale.classNumber_le, ← sq, hL_sq]
  obtain ⟨p₀, p₁, α, h_ne, hp₀, hp₁, h_norm⟩ := P.exists_prime_pair_norm s hW_pos h_classNumber_le
    fun U hU ↦ h_window U (by linarith [hU.1]) (by linarith [hU.2])
  have hg : ∀ i : Fin 2, P.IsPrincipalLevelPrime s L (![p₀, p₁] i) :=
    Fin.forall_fin_two.2 ⟨hp₀, hp₁⟩
  have hm_two : 2 ≤ m := mod_cast (by linarith : (2 : ℝ) ≤ m)
  obtain ⟨N, β, hN, hN_mod, hN_log, hβ⟩ := P.exists_prime_log_mem_Icc_mul_star_eq hm_two
    (by linarith) hL_sq hκ (hp₀.mul_mem_Icc hp₁) (h_scale.q₁_mul_d_le_exp hs hL.1)
    fun U hU ↦ h_window U (hm_mul.trans hU.1) hU.2
  exact ⟨m, r, s, b, T, ![p₀, p₁], α, N, β,
    { isLeast_m := by simpa [exp_half, exp_log hx_pos] using hm
      isLeast_r := by simpa [exp_five_mul_log hx_pos] using hr
      two_pow_eq := h_pow, isLeast_b := hb
      placeClass_eq_neg_one := h_class_T, towerDeg_le := by grw [h_card, hL.1]
      sparse := h_sparse
      levelPrime_prime i := (hg i).prime, levelPrime_modEq_one i := (hg i).modEq_one
      levelPrime_injective := Matrix.injective_pair_iff_ne.2 h_ne
      levelPrime_mem i := by simpa only [hb_eq] using (hg i).mem_Icc
      α_mul_star := h_norm
      N_prime := hN, N_modEq_one := hN_mod, log_N_mem := hN_log, β_mul_star := hβ }⟩

/-- **Existence of the data.** A term `D : Data P` consists of integer scales `x`, `x₁`, `b` with
`(log b) ^ 100 ≤ x`, `x ^ 10⁶ ≤ x₁` and `x₁ ^ 10⁶ ≤ b`, ranks `m`, `r`, the exponent `s` with
`2 ^ s = m ^ 22`, a large sparse set of infinite places of `E = K(ζ_{q₁})`, and primes `p₀ ≠ p₁`,
`N` of prescribed size and residue with `p₀ p₁ = α ᾱ` in `K = P.K` and `N = β β̄` in `E`. For
`0 < ε < 1 / 100` such a `D` exists at every large integer `x`, with `x₁ = ⌊exp (x ^ (ε / 6))⌋` and
`b` the least multiple of `q₁ x₁` that exceeds `exp (x ^ ε)`; `m` is the least power of `2` with
`m ≥ √x` and `r` the least power of `3` with `r ≥ x⁵`. Then `x ^ (ε / 6) - 1 ≤ log x₁` and
`x ^ ε ≤ log b ≤ x ^ ε + 1`. -/
theorem eventually_exists_data (P : Parameters) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data P,
      D.natX = x ∧
      D.natX₁ = ⌊exp ((x : ℝ) ^ (ε / 6))⌋₊ ∧
      IsLeast {b : ℕ | D.q₁ * D.natX₁ ∣ b ∧ exp ((x : ℝ) ^ ε) < b} D.natB ∧
      IsLeast {n : ℕ | (∃ j : ℕ, n = 2 ^ j) ∧ √x ≤ n} D.m ∧
      IsLeast {n : ℕ | (∃ j : ℕ, n = 3 ^ j) ∧ (x : ℝ) ^ 5 ≤ n} D.r ∧
      (x : ℝ) ^ (ε / 6) - 1 ≤ D.logX₁ ∧
      D.logB ∈ Set.Icc ((x : ℝ) ^ ε) ((x : ℝ) ^ ε + 1) := by
  obtain ⟨n, h_scale⟩ := P.exists_eventually_isLargeScale hε hε_lt
  have h_four : 4 ∣ P.q₀ * P.d := Dvd.dvd.mul_right (.trans (by norm_num) P.dvd_q₀) P.d
  have hW : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (ε / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h_scale, hW.eventually (exists_prime_modEq_one_log_mem _ (n + 7) h_four),
    eventually_exists_data_of_isAdmissibleData P hε hε_lt] with x hx h_window h_data
  -- admissible data exist, and they are the fields of the data `D`
  obtain ⟨m, r, s, b, T, g, α, N, β, h_adm⟩ := hx.exists_isAdmissibleData h_window
  obtain ⟨D, h_fields, h_logX₁, h_logB⟩ := h_data m r s b T g α N β h_adm
  obtain rfl : D.m = m := h_fields.m_eq
  obtain rfl : D.r = r := h_fields.r_eq
  obtain rfl : D.natB = b := h_fields.natB_eq
  obtain rfl : D.towerExp = s := h_fields.towerExp_eq
  have h_natB : IsLeast {b : ℕ | D.q₁ * D.natX₁ ∣ b ∧ exp ((x : ℝ) ^ ε) < b} D.natB := by
    simpa only [h_fields.natX₁_eq, rpow_div_six_pow_six] using h_adm.isLeast_b
  exact ⟨D, h_fields.natX_eq, h_fields.natX₁_eq, h_natB, h_adm.isLeast_m, h_adm.isLeast_r, h_logX₁,
    h_logB⟩

end New
