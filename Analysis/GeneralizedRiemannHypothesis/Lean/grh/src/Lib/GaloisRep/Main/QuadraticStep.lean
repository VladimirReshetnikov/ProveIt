import Lib.Adelic.Reduction.FirstMinimumShortBases
import Lib.ClassField.Grunwald

/-!
# Split places over ℚ(√−d) and quadratic steps with prescribed splitting

Let `K = ℚ(√-d)` (`New.QuadField` d, d ≡ 3 mod 4). For a CM field `E` containing `K`, we study the
places of `E` above split places of `K` prime to `d` (`New.GaloisRep.IsSplitPrimeToDisc`). For
stably unramified `E`, above each such place of `K` one can be chosen so that neither it nor its
conjugate equals one of two given places. We also construct a quadratic step `E'` over any stably
unramified CM field `E` (`New.HasPrimitiveRoot5040`: `E` contains a primitive 5040th root of unity).
The field `E'` contains `ℚ(√-D)` and has prescribed behaviour at the places over a given integer
`n`.

## Main definitions and results

* `New.GaloisRep.IsSplitPrimeToDisc.isSplit_of_below`: such a place differs from its complex
  conjugate.
* `New.GaloisRep.IsSplitPrimeToDisc.exists_place_above_ne`: if E satisfies
  `New.HasPrimitiveRoot5040`, each such place of K has a place of E above it such that neither it
  nor its conjugate equals one of two given places.
* `New.GaloisRep.exists_isQuadraticStep`, `New.GaloisRep.exists_isStep_hasQuadSubfield`: the step
  `E' = stepField χ`, for a character `χ` of `Gal(Ω/E)`, with the idele character of `χ`
  (`New.GaloisRep.IsQuadraticStep`).

Notions from other files:
* `New.GaloisRep.IsSplitPrimeToDisc`: The prime u of ℚ(√−d) contains an element x = (1 + √−d)/2 − b,
  b ∈ ℤ, that is coprime to its conjugate x̄.
* `New.IsStep`: A step `E'/E`: `E` is stably unramified, and `E'` is a CM field Galois over `E` of
  prime degree.
* `New.QZChar`: Continuous characters of a group with values in `New.QZ` = ℚ/ℤ; `QZ.mk r` is the
  class of `r : ℚ`, so `QZ.mk 2⁻¹` is `1 / 2`.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` for sources.
-/

namespace New.GaloisRep

/-!
## Places above split primes of ℚ(√−d)

`star w` is the complex conjugate of a place `w`, `New.FinPlace.q w` its norm and
`New.FinPlace.below w` the place below it; `w.IsSplit` says that `star w ≠ w`.
-/

section SplitPlaceCount

open NumberField Filter Ideal IsCyclotomicExtension.Rat Set Finset

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} [HasQuadSubfield d E]
  {w : FinPlace E}

/-- A place `w` of `E` above a split place of `ℚ(√−d)` prime to `d`
(`New.GaloisRep.IsSplitPrimeToDisc`) is split: it differs from its complex conjugate. -/
lemma IsSplitPrimeToDisc.isSplit_of_below (hw : IsSplitPrimeToDisc (w.below (QuadField d))) :
    w.IsSplit := by
  grind [below_star, isSplit_and_prime_q]

/-- For a finite set S of finite places of the CM field E and a nonzero natural number ℓ, almost all
finite places w satisfy three conditions. Neither w nor its complex conjugate lies in S, and ℓ does
not lie in the prime ideal of w. -/
lemma eventually_notMem_star_notMem (ℓ : ℕ) [NeZero ℓ] (S : Finset (FinPlace E)) :
    ∀ᶠ w : FinPlace E in cofinite, w ∉ S ∧ star w ∉ S ∧ ↑ℓ ∉ w.asIdeal := by
  filter_upwards [S.eventually_cofinite_notMem, S.finite_toSet.star.eventually_cofinite_notMem,
    (finite_natCast_mem (K := E) ℓ).eventually_cofinite_notMem] with w h h_star h_ℓ
  exact ⟨h, by simpa using h_star, h_ℓ⟩

/-- Let E contain a primitive 5040th root of unity and contain K = ℚ(√−d), let u be a split place of
K prime to d (`New.GaloisRep.IsSplitPrimeToDisc`), and let a, b be places of E. Then some place v of
E lies above u such that neither v nor its conjugate equals a or b. -/
lemma IsSplitPrimeToDisc.exists_place_above_ne [U : HasPrimitiveRoot5040 E]
    {u : FinPlace (QuadField d)} (hu : IsSplitPrimeToDisc u) (a b : FinPlace E) :
    ∃ v : FinPlace E, v.below (QuadField d) = u ∧ v ≠ a ∧ star v ≠ a ∧ v ≠ b ∧ star v ≠ b := by
  classical
  -- Otherwise only `a`, `b` and their conjugates lie over `p = u.q`. If `p ∤ m`, the field of
  -- `m`-th roots of unity then has at most four primes over `p`, unramified of degree the order of
  -- `p` modulo `m`. This is too few for `m = 80` and for `m = 63`, so `p` divides both.
  by_contra h_none
  obtain ⟨ζ, hζ⟩ := U.exists_primitive_root
  obtain ⟨-, hp, h_over⟩ := hu.isSplit_and_prime_q
  have : Fact u.q.Prime := ⟨hp⟩
  have h_four (v : FinPlace E) (hv : ↑u.q ∈ (v.below (QuadField d)).asIdeal) :
      v ∈ ({a, b, star a, star b} : Finset (FinPlace E)) := by
    grind [=_ below_star, star_star, (h_over (v.below _)).mpr hv]
  -- `k` is an exponent of the units modulo `m`, so it bounds the order of `p`.
  have h_dvd (m e : ℕ) (k : ℕ+) [NeZero m] (hm : 5040 = e * m) (hk : 4 * (k : ℕ) < m.totient)
      (h_exp : ∀ x : ZMod m, IsUnit x → x ^ (k : ℕ) = 1) : u.q ∣ m := by
    by_contra h_not
    obtain ⟨K, hK⟩ : ∃ K : IntermediateField ℚ E, IsCyclotomicExtension {m} ℚ K :=
      ⟨_, (hζ.pow (by lia) hm).intermediateField_adjoin_isCyclotomicExtension _⟩
    have h_primes : ((span {(u.q : ℤ)}).primesOver (𝓞 K)).ncard ≤ 4 := by
      have h_sub : (span {(u.q : ℤ)}).primesOver (𝓞 K) ⊆
          ↑(({a, b, star a, star b} : Finset (FinPlace E)).image fun v ↦ (v.below K).asIdeal) := by
        rintro P ⟨hP_prime, ⟨hP_over⟩⟩
        have hP_ne : P ≠ ⊥ := by aesop
        -- `P = v.below K` for some place `v` of `E`
        obtain ⟨v, ⟨⟩⟩ := FinPlace.comap_surjective (algebraMap K E) ⟨P, hP_prime, hP_ne⟩
        exact mem_image_of_mem _ (h_four v (by simpa using hP_over.le))
      grw [ncard_le_ncard h_sub, ncard_coe_finset, card_image_le, card_le_four]
    have h_order : orderOf (u.q : ZMod m) ≤ k :=
      orderOf_le_of_pow_eq_one k.pos (h_exp _ (ZMod.isUnit_prime_of_not_dvd hp h_not))
    -- `φ(m)` is the sum of `e f` over the primes above `p`, with `e = 1` and `f` the order of `p`.
    have h_sum :
        m.totient = ((span {(u.q : ℤ)}).primesOver (𝓞 K)).ncard * orderOf (u.q : ZMod m) := by
      rw [← finrank m K, ← RingOfIntegers.rank,
        ← sum_ramification_inertia_eq_finrank (span {(u.q : ℤ)})]
      simp [ramificationIdx_eq_of_not_dvd _ K _ h_not, inertiaDeg_eq_of_not_dvd _ K _ h_not]
    grw [h_sum, h_order, h_primes] at hk
    exact hk.false
  -- `φ(80) = 32` with exponent `4`, and `φ(63) = 36` with exponent `6`.
  have h80 : u.q ∣ 80 := h_dvd 80 63 4 rfl (by decide +kernel) (by decide +kernel)
  have h63 : u.q ∣ 63 := h_dvd 63 80 6 rfl (by decide +kernel) (by decide +kernel)
  exact hp.not_dvd_one (Nat.dvd_gcd h80 h63)

end SplitPlaceCount

/-!
## Existence of a quadratic step

`New.QZChar.stepField χ` is the field cut out by the character `symmetrise χ : g ↦ χ g + χ gᶜ`,
where `gᶜ` is the conjugate of `g` by complex conjugation `cmConj` on `Ω`, an algebraic closure of ℚ
into which `E` is embedded (`EmbeddedNumberField E`).
-/

section QuadraticStep

open NumberField IsDedekindDomain HeightOneSpectrum Ideal Nat ZMod decompGroup QZChar
  Cohomology QuadField algebraMap

/-- For `R ≠ 0` divisible by `4` and `n ≠ 0` there is `D ≡ -1 (mod R)` that is a norm `α * star α`
from `𝓞 E` and such that `-D` is a uniformiser at some place `P` prime to `n`. -/
lemma exists_norm_uniformiser (E : Type*) [Field E] [NumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] {R n : ℕ} (hR : R ≠ 0) (h4 : 4 ∣ R) (hn : n ≠ 0) :
    ∃ (D : ℕ) (α : 𝓞 E) (P : FinPlace E),
      R ∣ D + 1 ∧ α * star α = D ∧ ↑n ∉ P.asIdeal ∧
      P.valuation E ↑(-D : 𝓞 E) = WithZero.exp (-1) := by
  obtain ⟨i, ω, hi_sq, hi_star, hω_trace, hω_norm⟩ :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  -- With `b` the odd part of `R`, the norm `C` of `1 + 2 * b * ω` is odd and `1` mod `b`, so it is
  -- prime to `R`; moreover it is `3` mod `4`.
  obtain ⟨j, b, hb_odd, hRb⟩ := exists_eq_two_pow_mul_odd hR
  let C : ℕ := 1 + b * (2 + 8 * b)
  have hC4 : C % 4 = 3 := by grind
  have hC : C.Coprime R := by cases j <;> simp [hRb, C, coprime_mul_iff_right, parity_simps]
  -- Dirichlet: a large prime `q` with `C * q ≡ -1 (mod R)`. Then `q ≡ 1 (mod 4)`, so `q` is a sum
  -- of two squares, the norm of some `s + t * i`.
  have : NeZero R := ⟨hR⟩
  obtain ⟨q, hq_large, hq, hq_mod⟩ : ∃ q > C * n * absNorm (differentIdeal ℤ (𝓞 E)),
      q.Prime ∧ (q : ZMod R) = (-unitOfCoprime C hC)⁻¹ :=
    forall_exists_prime_gt_and_eq_mod (-unitOfCoprime C hC)⁻¹.isUnit _
  have hD : R ∣ C * q + 1 :=
    (natCast_eq_zero_iff ..).mp (by simp [hq_mod, neg_add_eq_zero])
  have : Fact q.Prime := ⟨hq⟩
  -- `4` divides `C * q + 1` and `C ≡ 3 (mod 4)`, so `q ≡ 1 (mod 4)`.
  have hq_mod_four : q % 4 ≠ 3 := by grind [h4.trans hD, Nat.mul_mod C q 4]
  obtain ⟨s, t, hst⟩ : ∃ s t : ℕ, s ^ 2 + t ^ 2 = q := Prime.sq_add_sq hq_mod_four
  -- A place `P` over `q`; being large, `q` divides none of `C`, `n` and the norm of the different.
  obtain ⟨P, hP⟩ := FinPlace.exists_natCast_mem E q
  obtain ⟨⟨hCP, hnP⟩, h_different⟩ :
      (↑C ∉ P.asIdeal ∧ ↑n ∉ P.asIdeal) ∧ ↑(absNorm (differentIdeal ℤ (𝓞 E))) ∉ P.asIdeal := by
    simpa [hq.dvd_mul, ← P.natCast_mem_iff_dvd hP, hn, C, NeZero.ne] using
      fun h ↦ eq_zero_of_dvd_of_lt h hq_large
  refine ⟨C * q, (1 + 2 * b * ω) * (s + t * i), P, hD, ?_, hnP, ?_⟩
  · -- The norm is multiplicative: `1 + 2 * b * ω` has norm `C` and `s + t * i` has norm `q`.
    have h_star : star ((1 + 2 * (b : 𝓞 E) * ω) * (s + t * i)) =
        (1 + 2 * (b : 𝓞 E) * star ω) * (s - t * i) := by simp [hi_star, sub_eq_add_neg]
    rw [h_star]
    push_cast [C, ← hst]
    linear_combination ((s : 𝓞 E) ^ 2 - (t : 𝓞 E) ^ 2 * i * i) *
        (2 * (b : 𝓞 E) * hω_trace + 4 * (b : 𝓞 E) ^ 2 * hω_norm) -
      (1 + 2 * (b : 𝓞 E) + 8 * (b : 𝓞 E) ^ 2) * (t : 𝓞 E) ^ 2 * hi_sq
  · -- `q` is unramified at `P`, since otherwise `P` would divide the different.
    have h_unram : ↑q ∉ P.asIdeal ^ 2 :=
      fun hq2 ↦ h_different (le_of_dvd (dvd_differentIdeal_of_mem_sq hq2) (absNorm_mem _))
    have hq_val : P.intValuation q = WithZero.exp (-1) := by
      simp [hP, h_unram, intValuation_eq_exp_neg_multiplicity,
        multiplicity_eq_of_dvd_of_not_dvd (k := 1), NeZero.ne]
    refine (valuation_of_algebraMap ..).trans ?_
    simp [hCP, hq_val]

/-- If `c ^ 2` lies in `E`, then every `g ∈ Gal(Ω/E)` sends `c` to `c` or to `-c`. -/
lemma apply_sqrt_eq_or_eq_neg {E : Type*} [Field E] [EmbeddedNumberField E] (g : Gal(Ω/E)) {c : Ω}
    {x : E} (hc : c ^ 2 = algebraMap E Ω x) :
    g c = c ∨ g c = -c :=
  eq_or_eq_neg_of_sq_eq_sq _ _ (by simp [← map_pow, hc])

open scoped Classical in
/-- The quadratic character of `E(b)`, where `b ≠ 0` and `b ^ 2 ∈ E`: its value at `g` is `0` if
`g b = b` and `1 / 2` otherwise. -/
lemma exists_qzChar_of_sq_eq {E : Type} [Field E] [EmbeddedNumberField E] {b : Ω} {x : E}
    (hb : b ^ 2 = algebraMap E Ω x) (hb0 : b ≠ 0) :
    ∃ χ : QZChar Gal(Ω/E),
      2 • χ = 0 ∧ ∀ g : Gal(Ω/E), χ.val g = if g b = b then 0 else QZ.mk 2⁻¹ := by
  have h_half_add : QZ.mk 2⁻¹ + QZ.mk 2⁻¹ = 0 := by
    simpa [two_smul] using (addOrderOf_eq_prime_iff.mp (QZ.addOrderOf_mk_inv two_pos)).left
  -- `g ↦ g b` takes only the values `b` and `-b`, and `g b = -b` multiplies like a sign.
  have h_cocycle (g h : Gal(Ω/E)) :
      (if (g * h) b = b then 0 else QZ.mk 2⁻¹) =
        (if g b = b then 0 else QZ.mk 2⁻¹) + if h b = b then 0 else QZ.mk 2⁻¹ := by
    cases apply_sqrt_eq_or_eq_neg g hb <;> cases apply_sqrt_eq_or_eq_neg h hb <;>
      simp [*, neg_eq_self]
  let χ : QZChar Gal(Ω/E) :=
    ⟨fun g ↦ if g b = b then 0 else .mk 2⁻¹,
      ((isLocallyConstant_smul b).comp fun c ↦ if c = b then 0 else QZ.mk 2⁻¹).continuous,
      fun g h ↦ by simpa using h_cocycle g h⟩
  refine ⟨χ, ?_, fun g ↦ rfl⟩
  ext
  simp [χ, ite_add_ite, h_half_add, two_smul]

/-- Local test: let `A` be a place of `Ω` over the place `w` of `E`. If `c ^ 2 = x` and
`1 - x * u ^ 2` lies in a power of `w` that does not contain `4`, then the decomposition group at
`A` fixes `c`. -/
lemma apply_sqrt_eq_self_of_mem_pow {E : Type*} [Field E] [EmbeddedNumberField E] {A : ClosurePlace}
    {w : FinPlace E} (hA : IsPlaceOver A w) {k : ℕ} (hk : 4 ∉ w.asIdeal ^ k) {g : Gal(Ω/E)}
    (hg : g ∈ decompGroup Gal(Ω/E) A) {c : Ω} {x u : 𝓞 E} (hc : c ^ 2 = algebraMap E Ω x)
    (hu : 1 - x * u ^ 2 ∈ w.asIdeal ^ k) :
    g c = c := by
  refine (apply_sqrt_eq_or_eq_neg g hc).resolve_right fun h_neg ↦ ?_
  -- Otherwise `g` exchanges `a = 1 + c * u` and `a' = 1 - c * u`, so these have the same valuation.
  let a : Ω := 1 + c * algebraMap E Ω u
  let a' : Ω := 1 - c * algebraMap E Ω u
  have h_swap : g • a = a' := by simp [a, a', h_neg, sub_eq_add_neg]
  have h_val : A.valuation a' = A.valuation a := by rw [← h_swap]; exact val_smul hg a
  have h_two : A.valuation (a' + a) ≤ A.valuation a := A.valuation.map_add_le h_val.le le_rfl
  -- Since `(a' + a) ^ 2 = 4` and `a * a' = 1 - x * u ^ 2`, this forces `4 ∈ w ^ k`.
  have h_sum : algebraMap E Ω (4 : 𝓞 E) = (a' + a) * (a' + a) := by norm_num [a, a', map_ofNat]
  have h_prod : algebraMap E Ω (1 - x * u ^ 2 : 𝓞 E) = a * a' := by
    simp [a, a', ← hc]
    ring
  have h_four : A.valuation (algebraMap E Ω (4 : 𝓞 E)) ≤
      A.valuation (algebraMap E Ω (1 - x * u ^ 2 : 𝓞 E)) := by
    simpa only [h_sum, h_prod, _root_.map_mul, h_val] using mul_le_mul' h_two h_two
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := E)] at hk hu
  exact hk (((hA.isEquiv ..).mp h_four).trans hu)

/-- Gluing at the places over `n`: let `α * star α = D` with `D ≡ -1 (mod w ^ k)` for all `w ∣ n`.
Then there is a nonzero real `t` such that at every `w ∣ n` either `α * t` is the inverse of a
square modulo `w ^ k`, or `star w = w` and `w` is prime to `2 * α * t`. -/
lemma exists_real_twist {E : Type*} [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E]
    {n k D : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) {α : 𝓞 E} (hα : α * star α = D)
    (hD : ∀ w : FinPlace E, ↑n ∈ w.asIdeal → ↑(D + 1) ∈ w.asIdeal ^ k) :
    ∃ t : 𝓞 E,
      t ≠ 0 ∧ star t = t ∧
      ∀ w : FinPlace E, ↑n ∈ w.asIdeal →
        (∃ u : 𝓞 E, 1 - α * t * u ^ 2 ∈ w.asIdeal ^ k) ∨
        star w = w ∧ α * t ∉ w.asIdeal ∧ 2 ∉ w.asIdeal := by
  obtain ⟨i, hi, -⟩ : ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  -- Order the places to pick one of each pair `w ≠ star w`, and choose `s ≡ α` at the larger one
  -- and `s ≡ 1` at the other places over `n`, modulo `w ^ k`.
  obtain ⟨_, -⟩ := exists_wellFoundedLT (FinPlace E)
  have : NeZero n := ⟨hn⟩
  obtain ⟨s, h_mod⟩ : ∃ s : 𝓞 E, ∀ w : FinPlace E, ↑n ∈ w.asIdeal →
      s - (if star w < w then α else 1) ∈ w.asIdeal ^ k := by
    simpa using exists_forall_sub_mem_ideal (s := (finite_natCast_mem n).toFinset) asIdeal
      (fun _ ↦ k) (by simp [prime]) (by grind [asIdeal_inj]) fun w ↦ if star w.val < w then α else 1
  have h_pow_le (w : FinPlace E) : w.asIdeal ^ k ≤ w.asIdeal := pow_le_self hk
  have h_mod_star (w : FinPlace E) (hw : ↑n ∈ w.asIdeal) :
      star s - (if w < star w then star α else 1) ∈ w.asIdeal ^ k := by
    simpa [starRingEnd_apply, apply_ite star] using le_comap_pow _ k (h_mod (star w) (by simpa))
  by_cases hs0 : s = 0
  · -- This happens only if no place divides `n`, for `s ≡ 1` at one of `w`, `star w`.
    refine ⟨1, one_ne_zero, star_one _, fun w hw ↦ absurd ?_ (one_notMem w.asIdeal)⟩
    grind [=_ Quotient.eq_zero_iff_mem, h_pow_le w (h_mod w hw), h_pow_le w (h_mod_star w hw),
      star_zero]
  refine ⟨s * star s, by simpa, by simp [mul_comm], fun w hw ↦ ?_⟩
  specialize hD w hw
  specialize h_mod w hw
  specialize h_mod_star w hw
  rcases lt_trichotomy w (star w) with hlt | heq | hgt
  · -- `s ≡ 1` and `star s ≡ star α`, so `α * t ≡ D ≡ -1 = i ^ 2`.
    refine .inl ⟨i, ?_⟩
    grind [=_ Quotient.eq_zero_iff_mem, congrArg (Ideal.Quotient.mk (w.asIdeal ^ k)) hi]
  · refine .inr ⟨heq.symm, fun h ↦ one_notMem w.asIdeal ?_, fun h_two ↦ ?_⟩
    · -- `s ≡ star s ≡ 1`, so `α * t * star α ≡ D ≡ -1` is not in `w`.
      grind [=_ Quotient.eq_zero_iff_mem, h_pow_le w hD, h_pow_le w h_mod, h_pow_le w h_mod_star]
    · exact HasPrimitiveRoot5040.isSplit_of_two_mem h_two heq.symm
  · -- `s ≡ α` and `star s ≡ 1`, so `α * t * star α ^ 2 ≡ D ^ 2 ≡ 1`.
    exact .inl ⟨star α, by grind [=_ Quotient.eq_zero_iff_mem]⟩

/-- A place of `ℚ(√-D)` that contains `(D + 1) / 4` is split and prime to `D`. -/
lemma IsSplitPrimeToDisc.of_mem {D : ℕ} [Fact (D % 4 = 3)] {v : FinPlace (QuadField D)}
    (hv_mem : ↑((D + 1) / 4) ∈ v.asIdeal) :
    IsSplitPrimeToDisc v := by
  -- With `betaK = (1 + √-D) / 2`, the prime `v` contains `betaK * (1 - betaK)`, hence `betaK` or
  -- `betaK - 1`. As `star betaK = 1 - betaK`, each adds up with its conjugate to `1` or `-1`, so it
  -- is coprime to it.
  have h_prod : betaK D * (1 - betaK D) ∈ v.asIdeal := by rwa [betaK_mul_one_sub D]
  obtain hc | hc := v.isPrime.mem_or_mem h_prod
  · -- `b = 0`: `x = betaK` lies in `v`, and `x + star x = 1`
    exact ⟨0, by simpa using hc, 1, 1, by simp⟩
  · -- `b = 1`: `x = betaK - 1` lies in `v`, and `x + star x = -1`
    exact ⟨1, by simpa using neg_mem hc, -1, -1, by simp⟩

/-- The inertia group at a place `A` of `Ω` lies in the decomposition group at `A`. -/
lemma inertiaGroup_le_decompGroup {E : Type*} [Field E] [EmbeddedNumberField E] {A : ClosurePlace} :
    inertiaGroup Gal(Ω/E) A ≤ decompGroup Gal(Ω/E) A :=
  fun _ hg_inertia ↦ hg_inertia.left

/-- Let `b ^ 2 = α * t`, and let `A` be a place of `Ω` over the place `w` of `E`, where `4 ∉ w ^ k`.
Suppose that `1 - α * t * u ^ 2 ∈ w ^ k` for some `u`, or that `star w = w`, `α * t ∉ w` and
`2 ∉ w`. Then the inertia group at `A` fixes `b`: by `apply_sqrt_eq_self_of_mem_pow` in the first
case, and because `b ^ 2` and `2` are units at `A` in the second. -/
lemma apply_eq_of_mem_inertiaGroup_of_sq_eq {E : Type} [Field E] [EmbeddedNumberField E]
    [IsCMField E] {A : ClosurePlace} {w : FinPlace E} (hA : IsPlaceOver A w) {k : ℕ}
    (hk : 4 ∉ w.asIdeal ^ k) {α t : 𝓞 E} {b : Ω} (hb : b ^ 2 = algebraMap E Ω ↑(α * t))
    (h_local : (∃ u : 𝓞 E, 1 - α * t * u ^ 2 ∈ w.asIdeal ^ k) ∨
      star w = w ∧ α * t ∉ w.asIdeal ∧ 2 ∉ w.asIdeal)
    {g : Gal(Ω/E)} (hg : g ∈ inertiaGroup Gal(Ω/E) A) :
    g b = b := by
  rcases h_local with ⟨u, hu⟩ | ⟨-, hαt, h2⟩
  · exact apply_sqrt_eq_self_of_mem_pow hA hk (inertiaGroup_le_decompGroup hg) hb hu
  · have h2_val : A.valuation (2 : Ω) = 1 := hA.valuation_natCast_eq_one_iff.mpr h2
    have hαt_val : A.valuation (algebraMap E Ω ↑(α * t)) = 1 :=
      hA.valuationVia_eq_one_iff.mpr ((valuation_eq_one_iff_notMem ..).mpr hαt)
    have h_fix : g • algebraMap E Ω ↑(α * t) = algebraMap E Ω ↑(α * t) := by simp
    exact inertia_fixes_root_of_unit hg h2_val hb hαt_val h_fix

/-- Let `b ^ 2 = α * t`, and let `A` be a place of `Ω` over the place `w` of `E`, where `4 ∉ w ^ k`.
Suppose that `1 - α * t * u ^ 2 ∈ w ^ k` for some `u`, or that `star w = w`, `α * t ∉ w` and
`2 ∉ w`. If `w` is split (`star w ≠ w`), which excludes the second case, then the decomposition
group at `A` fixes `b`. -/
lemma apply_eq_of_mem_decompGroup_of_sq_eq {E : Type} [Field E] [EmbeddedNumberField E]
    [IsCMField E] {A : ClosurePlace} {w : FinPlace E} (hA : IsPlaceOver A w) {k : ℕ}
    (hk : 4 ∉ w.asIdeal ^ k) {α t : 𝓞 E} {b : Ω} (hb : b ^ 2 = algebraMap E Ω ↑(α * t))
    (h_local : (∃ u : 𝓞 E, 1 - α * t * u ^ 2 ∈ w.asIdeal ^ k) ∨
      star w = w ∧ α * t ∉ w.asIdeal ∧ 2 ∉ w.asIdeal)
    (h_split : w.IsSplit) {g : Gal(Ω/E)} (hg : g ∈ decompGroup Gal(Ω/E) A) :
    g b = b := by
  obtain ⟨u, hu⟩ : ∃ u : 𝓞 E, 1 - α * t * u ^ 2 ∈ w.asIdeal ^ k :=
    h_local.resolve_right fun ⟨h_star_eq, _⟩ ↦ h_split h_star_eq
  exact apply_sqrt_eq_self_of_mem_pow hA hk hg hb hu

/-- Let `i * i = -1`, let `t ≠ 0` be real, let `α * star α = D`, and let `b ^ 2 = α * t` and
`cmConj b ^ 2 = star (α * t)`. Then `y = (i / t) * b * cmConj b` is a square root of `-D`. -/
lemma sq_eq_neg_natCast_of_sq_eq_mul {E : Type} [Field E] [EmbeddedNumberField E] [IsCMField E]
    {i α t : 𝓞 E} {D : ℕ} (hi_sq : i * i = -1) (ht : t ≠ 0) (ht_real : star t = t)
    (hα : α * star α = D) {b : Ω} (hb : b ^ 2 = algebraMap E Ω ↑(α * t))
    (hb_conj : cmConj b ^ 2 = algebraMap E Ω (star ↑(α * t))) :
    (algebraMap E Ω (i / t) * b * cmConj b) ^ 2 = algebraMap E Ω (-D : 𝓞 E) := by
  simp_rw [mul_pow, hb, hb_conj, ← map_pow, ← _root_.map_mul]
  congr
  field_simp (disch := simp [ht])
  norm_cast
  grind [star_mul]

open scoped Classical in
/-- Let `χ` be the quadratic character of `E(b)` (`hχ`), where `b ≠ 0`, `b ^ 2 = x` and
`cmConj b ^ 2 = star x`, and let `c ≠ 0` in `E`. Then `symmetrise χ` vanishes at `g` exactly when
`g` fixes `c * b * cmConj b`: both say that `g` has the same sign on `b` and on `cmConj b`. -/
lemma symmetrise_apply_eq_zero_iff {E : Type} [Field E] [EmbeddedNumberField E] [IsCMField E]
    {χ : QZChar Gal(Ω/E)} {b : Ω} {x : 𝓞 E}
    (hχ : ∀ g : Gal(Ω/E), χ.val g = if g b = b then 0 else QZ.mk 2⁻¹)
    (hb : b ^ 2 = algebraMap E Ω ↑x) (hb_conj : cmConj b ^ 2 = algebraMap E Ω (star ↑x))
    (hb0 : b ≠ 0) {c : E} (hc : c ≠ 0) (g : Gal(Ω/E)) :
    (symmetrise χ).val g = 0 ↔
      g (algebraMap E Ω c * b * cmConj b) = algebraMap E Ω c * b * cmConj b := by
  obtain ⟨h_half_add, h_half_ne⟩ : QZ.mk 2⁻¹ + QZ.mk 2⁻¹ = 0 ∧ QZ.mk 2⁻¹ ≠ 0 := by
    simpa [two_smul] using addOrderOf_eq_prime_iff.mp (QZ.addOrderOf_mk_inv two_pos)
  cases apply_sqrt_eq_or_eq_neg g hb <;> cases apply_sqrt_eq_or_eq_neg g hb_conj <;>
    simp [*, conjGal, QZChar.comap, neg_eq_self]

open scoped Classical in
/-- Let `E` be a CM field and `χ` the character of `Gal(Ω/E)` that is `0` at the `g` with `g b = b`
and `1 / 2` elsewhere. Let `symmetrise χ` be `g ↦ χ g + χ gᶜ`, where `gᶜ` is the conjugate of `g` by
complex conjugation `cmConj` on `Ω`, an algebraic closure of ℚ into which `E` is embedded
(`EmbeddedNumberField E`). Let `P` be a finite place with `n ∉ P`, let `σ` lie in the inertia group
at `placeOver P` (a chosen place of `Ω` over `P`) with `symmetrise χ σ ≠ 0`, and let the subgroup
`H` contain the inertia groups at all places of `Ω` above finite places of `E` prime to `n` of norm
`q` at most that of `P`; then every `g` has some `h ∈ H` with `g * h` in the kernels of both
`symmetrise χ` and `χ`. -/
lemma exists_mul_mem_ker_symmetrise_inf_ker {E : Type} [Field E] [EmbeddedNumberField E]
    [IsCMField E] {χ : QZChar Gal(Ω/E)} {b : Ω}
    (hχ : ∀ g : Gal(Ω/E), χ.val g = if g b = b then 0 else QZ.mk 2⁻¹) {n : ℕ} {P : FinPlace E}
    (hnP : ↑n ∉ P.asIdeal) {σ : decompGroup Gal(Ω/E) (placeOver P)}
    (hσ_inertia : σ ∈ inertiaGroup (decompGroup Gal(Ω/E) (placeOver P)) (placeOver P))
    (hσ_sym : (symmetrise χ).val σ ≠ 0) {H : Subgroup Gal(Ω/E)}
    (hH : inertiaAbove {x : FinPlace E | ↑n ∉ x.asIdeal ∧ x.q ≤ P.q} ⊆ H) (g : Gal(Ω/E)) :
    ∃ h ∈ H, g * h ∈ ker (symmetrise χ) ⊓ ker χ := by
  -- `H` contains `σ` (inertia over `P`) and `conjGal σ` (inertia over `star P`).
  have hσH : (σ : Gal(Ω/E)) ∈ H := hH ⟨P, by simp [hnP], _, P.isPlaceOver_placeOver, hσ_inertia⟩
  have hσH' : conjGal (σ : Gal(Ω/E)) ∈ H :=
    hH ⟨star P, by simp [hnP], _, P.isPlaceOver_placeOver.conjPlace_star,
      hσ_inertia.conjPlace_conjGal⟩
  obtain ⟨h_half_add, h_half_ne⟩ : QZ.mk 2⁻¹ + QZ.mk 2⁻¹ = 0 ∧ QZ.mk 2⁻¹ ≠ 0 := by
    simpa [two_smul] using addOrderOf_eq_prime_iff.mp (QZ.addOrderOf_mk_inv two_pos)
  -- membership in `QZChar` is continuity and the cocycle identity, here for the trivial action
  obtain ⟨-, h_mul⟩ := χ.property
  -- The subgroup in the goal is the kernel of `g ↦ (χ g, χ (conjGal g))`, with values in
  -- `{0, 1 / 2} ^ 2`. By `hσ_sym` the images of `σ` and `conjGal σ` are `(1 / 2, 0)` and
  -- `(0, 1 / 2)` in some order, so some `σ ^ a * conjGal σ ^ c` cancels the image of `g`.
  have h_mem (g' : Gal(Ω/E)) :
      g' ∈ ker (symmetrise χ) ⊓ ker χ ↔ χ.val g' = 0 ∧ χ.val (conjGal g') = 0 := by
    change χ.val g' + χ.val (conjGal g') = 0 ∧ χ.val g' = 0 ↔ _
    grind
  obtain ⟨a, c, hac⟩ : ∃ a c : Fin 2,
      g * ((σ : Gal(Ω/E)) ^ (a : ℕ) * conjGal (σ : Gal(Ω/E)) ^ (c : ℕ)) ∈
        ker (symmetrise χ) ⊓ ker χ := by
    revert hσ_sym
    -- The goal becomes a disjunction over the four choices of `a` and `c`; it is a case check over
    -- the values `0` and `1 / 2` of `χ` at `g`, `conjGal g`, `σ` and `conjGal σ`.
    simp [-Subgroup.mem_inf, h_mem, h_mul, QZChar.comap, hχ]
    split_ifs <;> simp [*]
  exact ⟨_, mul_mem (pow_mem hσH a) (pow_mem hσH' c), hac⟩

/-- Let `k` be the norm of the ideal `(4)`. No power `w ^ k` of a finite place `w` contains `4`:
else `N(w) ^ k` would divide the norm of `4`, whose absolute value is `k`, while
`N(w) ^ k ≥ 2 ^ k > k`. -/
lemma four_notMem_pow_absNorm_span_four {E : Type*} [Field E] [NumberField E] (w : FinPlace E) :
    4 ∉ w.asIdeal ^ (span {(4 : 𝓞 E)}).absNorm := by
  intro h_mem
  have h_le : w.q ^ (Algebra.norm ℤ (4 : 𝓞 E)).natAbs ≤ (Algebra.norm ℤ (4 : 𝓞 E)).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero (absNorm_dvd_norm_of_mem h_mem) (by simp)
  exact not_le.mpr (Nat.lt_pow_self w.one_lt_q) h_le

/-- Let `x ≠ 0` in `𝓞 E` be a uniformiser at the place `P`, and let `y ^ 2 = x`. Then some `σ` in
the inertia group at `placeOver P` (a place of `Ω` over `P`) sends `y` to `-y`. -/
lemma exists_mem_inertiaGroup_smul_eq_neg {E : Type} [Field E] [EmbeddedNumberField E]
    [IsCMField E] {P : FinPlace E} {x : 𝓞 E} (hx_ne : (x : E) ≠ 0)
    (hP : P.valuation E ↑x = WithZero.exp (-1)) {y : Ω} (hy : y ^ 2 = algebraMap E Ω ↑x) :
    ∃ σ ∈ inertiaGroup (decompGroup Gal(Ω/E) (placeOver P)) (placeOver P), σ • y = -y := by
  -- `x` stays a uniformiser of the decomposition field, and inertia is transitive on the square
  -- roots of a uniformiser.
  obtain ⟨h_local, -, h_unif⟩ :=
    P.isPlaceOver_placeOver.isLocalGalois_and_residueCard_eq_and_isUniformiser Gal(Ω/E)
  exact h_local.exists_inertia_smul_eq_of_pow_eq
    (h_unif (π := .mk0 (x : E) hx_ne) (P.isPlaceOver_placeOver.isUniformiser_iff.mpr hP))
    two_pos hy (neg_sq y)

/-- A `ℚ/ℤ`-valued character `χ` of `Gal(Ω/E)` and a natural number `D` form a quadratic step over
`E` for the integer `n`. Here `symmetrise χ` is `g ↦ χ g + χ gᶜ`, with `gᶜ` the conjugate of `g` by
complex conjugation, and `stepField χ`, the fixed field of its kernel, contains `ℚ(√-D)`. -/
structure IsQuadraticStep (E : Type) [Field E] [EmbeddedNumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] (n : ℕ) (χ : QZChar Gal(Ω/E)) (D : ℕ)
    [HasQuadSubfield D (stepField χ)] : Prop where
  /-- `stepField χ`, with the idele character of `χ`, is a step over `E`. -/
  isStep : IsStep (stepField χ) (ideleChar χ)
  /-- For some `m`, every subgroup that contains the inertia groups at the places prime to `n` of
  norm at most `m` generates `Gal(Ω/E)` together with `ker (symmetrise χ) ⊓ ker χ`. -/
  exists_mul_mem_of_inertiaAbove_subset : ∃ m : ℕ, ∀ H : Subgroup Gal(Ω/E),
    inertiaAbove {x : FinPlace E | ↑n ∉ x.asIdeal ∧ x.q ≤ m} ⊆ H →
    ∀ g : Gal(Ω/E), ∃ h ∈ H, g * h ∈ ker (symmetrise χ) ⊓ ker χ
  /-- The places of `stepField χ` over `n` lie over split places of `QuadField D` prime to `D`. -/
  isSplitPrimeToDisc_below : ∀ u : FinPlace (stepField χ), ↑n ∈ u.asIdeal →
    IsSplitPrimeToDisc (u.below (QuadField D))
  /-- At a place over `n`, the decomposition group fixes `stepField χ`. -/
  decompGroup_le_ker_symmetrise : ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w →
    ↑n ∈ w.asIdeal → decompGroup Gal(Ω/E) A ≤ ker (symmetrise χ)
  /-- At a place over `n`, the inertia group fixes `stepField χ`, and `χ` vanishes on it. -/
  inertiaGroup_le_ker_inf : ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w →
    ↑n ∈ w.asIdeal → inertiaGroup Gal(Ω/E) A ≤ ker (symmetrise χ) ⊓ ker χ
  /-- At a split place over `n`, the same holds for the whole decomposition group. -/
  decompGroup_le_ker_inf_of_isSplit : ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w →
    ↑n ∈ w.asIdeal → w.IsSplit → decompGroup Gal(Ω/E) A ≤ ker (symmetrise χ) ⊓ ker χ

/-- For `E` a CM field containing a primitive 5040th root of unity (`HasPrimitiveRoot5040 E`) and
`n ≠ 0`, there are a `ℚ/ℤ`-valued character `χ` of `Gal(Ω/E)` and `D ≡ 3 (mod 4)` with the following
properties. The field `stepField χ`, the fixed field of the kernel of `g ↦ χ g + χ gᶜ` (`gᶜ` is the
conjugate of `g` by complex conjugation), contains `ℚ(√-D)`. Moreover `χ` and `D` form a quadratic
step over `E` for `n` (`New.GaloisRep.IsQuadraticStep`): `stepField χ` is a step over `E` with
prescribed splitting and ramification at the places over `n`. -/
lemma exists_isQuadraticStep (E : Type) [Field E] [EmbeddedNumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] (n : ℕ) (hn : n ≠ 0) :
    ∃ (χ : QZChar Gal(Ω/E)) (D : ℕ) (_ : HasQuadSubfield D (stepField χ)),
      IsQuadraticStep E n χ D := by
  classical
  -- `χ` is the quadratic character of `E(b)`, `b ^ 2 = α * t`, where `α * star α = D` and `t` is
  -- real; then `stepField χ = E(√-D)`. The congruence `D ≡ -1` and the choice of `t` give the
  -- conditions over `n`; ramification of `√-D` at a place `P` prime to `n` gives the generation by
  -- inertia.
  obtain ⟨i, hi_sq, -⟩ := HasPrimitiveRoot5040.exists_mul_self_eq_neg_one (E := E)
  have hi : i ≠ 0 := by grind
  -- With `k` the norm of `4`, no `w ^ k` contains `4`: its norm is at least `2 ^ k > k`.
  let k : ℕ := (span {(4 : 𝓞 E)}).absNorm
  have hk (w : FinPlace E) : 4 ∉ w.asIdeal ^ k := four_notMem_pow_absNorm_span_four w
  -- The modulus makes `D ≡ 3 (mod 4)`, `n ∣ (D + 1) / 4` and `D ≡ -1 (mod w ^ k)` for `w ∣ 2 * n`.
  obtain ⟨D, α, P, ⟨M, hM⟩, hα, hnP, hP⟩ : ∃ (D : ℕ) (α : 𝓞 E) (P : FinPlace E),
      4 * n * (2 * n) ^ k ∣ D + 1 ∧ α * star α = D ∧ ↑n ∉ P.asIdeal ∧
      P.valuation E ↑(-D : 𝓞 E) = WithZero.exp (-1) :=
    exists_norm_uniformiser E (by positivity) ((dvd_mul_right 4 n).mul_right _) hn
  have hD4 : Fact (D % 4 = 3) := ⟨by grind⟩
  have hD (w : FinPlace E) (hw : 2 ∈ w.asIdeal ∨ ↑n ∈ w.asIdeal) : ↑(D + 1) ∈ w.asIdeal ^ k := by
    simp [hM, pow_mem_pow (w.isPrime.mul_mem_iff_mem_or_mem.mpr hw), mul_mem_left, mul_mem_right]
  obtain ⟨t, ht, ht_real, ht_local⟩ :=
    exists_real_twist hn (by simp [k]) hα fun w hw ↦ hD w (.inr hw)
  -- `(b * cmConj b) ^ 2 = D * t ^ 2`, so `y` below is a square root of `-D`.
  obtain ⟨b, hb⟩ := Variety.IsAbsIntegrallyClosed.exists_pow_eq 2 (algebraMap E Ω ↑(α * t))
  have hb_conj : cmConj b ^ 2 = algebraMap E Ω (star ↑(α * t)) := by
    rw [← map_pow, hb, cmConj_algebraMap]
  let y : Ω := algebraMap E Ω (i / t) * b * cmConj b
  have hy : y ^ 2 = algebraMap E Ω (-D : 𝓞 E) :=
    sq_eq_neg_natCast_of_sq_eq_mul hi_sq ht ht_real hα hb hb_conj
  have hy0 : y ≠ 0 := by
    simpa using hy.trans_ne (show algebraMap E Ω (-D : 𝓞 E) ≠ 0 by simp [NeZero.ne])
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hy0)
  -- The character: `χ g` is `0` or `1 / 2` according as `g b = b` or `g b = -b`.
  obtain ⟨χ, hχ_two, hχ⟩ := exists_qzChar_of_sq_eq hb hb0
  have hχ_ker {g : Gal(Ω/E)} (hg : g b = b) : g ∈ ker χ := (hχ g).trans (ite_eq_left hg)
  -- `symmetrise χ` vanishes at `g` iff `g` has the same sign on `b` and on `cmConj b`, iff `g`
  -- fixes `y`.
  have h_sym (g : Gal(Ω/E)) : (symmetrise χ).val g = 0 ↔ g y = y :=
    symmetrise_apply_eq_zero_iff hχ hb hb_conj hb0 (by simp [hi, ht]) g
  -- The local test with `1 - (-D) * 1 ^ 2 = D + 1`: decomposition groups over `2 * n` fix `y`.
  have h_dec {A : ClosurePlace} {w : FinPlace E} (hA : IsPlaceOver A w)
      (hw : 2 ∈ w.asIdeal ∨ ↑n ∈ w.asIdeal) : decompGroup Gal(Ω/E) A ≤ ker (symmetrise χ) := by
    exact fun g hg ↦ (h_sym g).mpr <|
      apply_sqrt_eq_self_of_mem_pow hA (hk w) hg hy (u := 1) (by simpa [add_comm] using hD w hw)
  -- As `-D` is a uniformiser at `P`, some `σ` in the inertia group over `P` sends `y` to `-y`.
  obtain ⟨σ, hσ_inertia, hσ⟩ := exists_mem_inertiaGroup_smul_eq_neg (by simp [NeZero.ne]) hP hy
  have hσ_sym : (symmetrise χ).val σ ≠ 0 :=
    mt (h_sym σ).mp (hσ.trans_ne (by simpa [neg_eq_self] using hy0))
  -- The step comes from `isStep_stepField`: `2 • χ = 0`, and `symmetrise χ` is nonzero and
  -- unramified above `2`.
  have h_sym_ne : symmetrise χ ≠ 0 := fun h_zero ↦ hσ_sym (by simp [h_zero])
  obtain ⟨h_step, -⟩ := isStep_stepField χ prime_two hχ_two h_sym_ne fun hA hw g hg ↦
      h_dec hA (.inl hw) (inertiaGroup_le_decompGroup hg)
  -- `y` lies in `stepField χ`, which therefore contains `ℚ(√-D)`.
  let y' : stepField χ := ⟨y, fun g ↦ (h_sym _).mp g.prop⟩
  have hy'_sq : y' ^ 2 = -(D : stepField χ) := Subtype.ext (by simp [y', hy])
  let : Algebra (QuadField D) (stepField χ) := (embOfSqrt D (y := y') hy'_sq).toAlgebra
  let h_quad : HasQuadSubfield D (stepField χ) := {}
  refine ⟨χ, D, h_quad,
    { isStep := h_step
      exists_mul_mem_of_inertiaAbove_subset := ⟨P.q, fun H hH g ↦ ?_⟩
      isSplitPrimeToDisc_below := ?_
      decompGroup_le_ker_symmetrise := fun hA hw ↦ h_dec hA (.inr hw)
      inertiaGroup_le_ker_inf := fun {A w} hA hw g hg ↦
        ⟨h_dec hA (.inr hw) (inertiaGroup_le_decompGroup hg), hχ_ker ?_⟩
      decompGroup_le_ker_inf_of_isSplit := fun {A w} hA hw h_split g hg ↦
        ⟨h_dec hA (.inr hw) hg, hχ_ker ?_⟩ }⟩
  · -- `H` contains `σ` and `conjGal σ`, inertia over `P` and over `star P`.
    exact exists_mul_mem_ker_symmetrise_inf_ker hχ hnP hσ_inertia hσ_sym hH g
  · -- A place over `n` contains `(D + 1) / 4`.
    simp +contextual [IsSplitPrimeToDisc.of_mem, hM, mul_assoc, mul_mem_right]
  · -- Inertia at `w ∣ n` fixes `b`.
    exact apply_eq_of_mem_inertiaGroup_of_sq_eq hA (hk w) hb (ht_local w hw) hg
  · -- At a split `w` the local test applies to the whole decomposition group.
    exact apply_eq_of_mem_decompGroup_of_sq_eq hA (hk w) hb (ht_local w hw) h_split hg

/-- For `E` a CM field with `HasPrimitiveRoot5040 E` and `n ≠ 0` there are a character `χ` of
`G_E = Gal(Ω/E)` and `D ≡ 3 (mod 4)` such that `E' = stepField χ` contains `ℚ(√-D)` and has the
properties (a)–(d) below, where `U` is the kernel of `symmetrise χ` and `N = U ⊓ ker χ`;
`inertiaAbove S` holds the inertia groups at the places of `Ω` above places in `S`. These are the
fields of `New.GaloisRep.IsQuadraticStep`, written out. -/
lemma exists_isStep_hasQuadSubfield (E : Type) [Field E] [EmbeddedNumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] (n : ℕ) (hn : n ≠ 0) :
    ∃ χ : QZChar Gal(Ω/E),
      let E' : IntermediateField E Ω := stepField χ
      let U : Subgroup Gal(Ω/E) := ker (symmetrise χ)
      let N : Subgroup Gal(Ω/E) := U ⊓ ker χ
      ∃ (D : ℕ) (_ : HasQuadSubfield D E'),
        -- (a) `E'` is a step over `E`
        IsStep E' (ideleChar χ) ∧
        -- (b) inertia away from `n` generates `Gal(Ω/E)` modulo `N`
        (∃ m : ℕ, ∀ H : Subgroup Gal(Ω/E),
          inertiaAbove {x : FinPlace E | ↑n ∉ x.asIdeal ∧ x.q ≤ m} ⊆ H →
          ∀ g : Gal(Ω/E), ∃ h ∈ H, g * h ∈ N) ∧
        -- (c) the places of `E'` over `n` lie over split places of `QuadField D`
        (∀ u : FinPlace E', ↑n ∈ u.asIdeal → IsSplitPrimeToDisc (u.below (QuadField D))) ∧
        -- (d) decomposition and inertia groups at the places of `E` over `n`
        ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w → ↑n ∈ w.asIdeal →
          decompGroup Gal(Ω/E) A ≤ U ∧
          inertiaGroup Gal(Ω/E) A ≤ N ∧
          (w.IsSplit → decompGroup Gal(Ω/E) A ≤ N) := by
  obtain ⟨χ, D, h_sub, h_step⟩ := exists_isQuadraticStep E n hn
  exact ⟨χ, D, h_sub, h_step.isStep, h_step.exists_mul_mem_of_inertiaAbove_subset,
    h_step.isSplitPrimeToDisc_below, fun hA hw ↦ ⟨h_step.decompGroup_le_ker_symmetrise hA hw,
      h_step.inertiaGroup_le_ker_inf hA hw, h_step.decompGroup_le_ker_inf_of_isSplit hA hw⟩⟩

end QuadraticStep

end New.GaloisRep
