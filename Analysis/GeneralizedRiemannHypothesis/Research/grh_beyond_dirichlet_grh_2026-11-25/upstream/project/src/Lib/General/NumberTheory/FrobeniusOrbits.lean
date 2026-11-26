import Lib.Adelic.Adeles.Basic

/-!
# Frobenius orbits of roots over finite fields and residue fields at self-conjugate places

This file collects arithmetic lemmas on finite fields and on finite places of a CM field `E`. For
`P` irreducible over a finite field with `q` elements and a root `x` of `P` in an extension `K`, the
roots of `P` in `K` are the Frobenius conjugates `x^(q^i)`, `i < deg P`. For a CM field `E` with a
primitive root of unity of order `5040`, a place fixed by conjugation has a norm that is a square,
so places of prime norm are split. The file also contains two summation lemmas.

* `New.FinPlace E`: the finite places `w` of `E`, that is, the nonzero primes of `𝓞 E`; `star w` is
  the complex conjugate of `w`.
* `w.q`: the norm of `w`, that is, the number of elements of its residue field.
* `w.IsSplit`: the statement `star w ≠ w`.

## Main definitions and results

* `New.card_selfAdjoint`: the size of a finite field with an involution that moves `√-1`.
* `New.two_notMem_of_star_eq`: if `E` contains an integer of trace `1` and even norm over its
  maximal real subfield, a place with `star w = w` does not lie above `2`;
  `New.HasPrimitiveRoot5040.isSplit_of_two_mem` is the case of the hypothesis
  `New.HasPrimitiveRoot5040 E`.
* `New.exists_sq_eq_q_of_star_eq`: if moreover `E` contains `√-1`, such a place has norm
  `w.q = r ^ 2` with `r % 4 = 3`; `New.HasPrimitiveRoot5040.exists_sq_eq_q_of_inert` is the case
  of the hypothesis `New.HasPrimitiveRoot5040 E`.
* `New.finite_prime_q_star_eq`, `New.isSplit_of_q_prime`: all but finitely many places of prime norm
  are moved by the conjugation, and all of them under the hypothesis `New.HasPrimitiveRoot5040 E`.
* `New.root_pow_card_pow_eq_self_iff`, `New.root_pow_card_pow_eq_iff_modEq`: `x^(q^n) = x` iff
  `deg P ∣ n`, and `x^(q^a) = x^(q^b)` iff `a ≡ b` modulo `deg P`.
* `New.aroots_eq_frobenius_orbit`, `New.aroots_pow_eq_frobenius_orbit`: with multiplicity, the roots
  of `P` in `K` are the `x^(q^i)` for `i < deg P`, and the roots of `P^j` are the `x^(q^i)` for
  `i < deg (P^j)`.

## Relation to the literature

Known: standard facts on finite fields and on residue fields of CM fields.
-/

/-! ## Integer powers with a sum as exponent -/

/-- For a nonzero element `s` of a field, a power of `s` whose integer exponent is a finite sum is
the product of the powers of `s`. -/
theorem New.DiscreteSeries.zpow_sum_of_ne_zero {ι K : Type*} [Field K] {s : K} (hs : s ≠ 0)
    (t : Finset ι) (f : ι → ℤ) : s ^ ∑ i ∈ t, f i = ∏ i ∈ t, s ^ f i := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hs, ih]

/-!
## Residue fields at self-conjugate places of a CM field

A count of the fixed points of an involution of a finite field, applied to the residue fields at
the finite places of a CM field `E` fixed by complex conjugation. If `E` has a primitive root of
unity of order `5040`, its integers contain a square root `i` of `-1` with `star i = -i`, and an `ω`
with `ω + star ω = 1` and `ω * star ω` even.
-/

section InertResidue

open Nat NumberField New HasPrimitiveRoot5040 FiniteField Ideal Quotient selfAdjoint

/-- A finite field with an involution that moves a square root of `-1` has `r ^ 2` elements,
where `r`, the number of fixed points, is `3` modulo `4`. -/
lemma New.card_selfAdjoint {k : Type*} [Field k] [StarRing k] [Finite k] {i : k}
    (hi_sq : i * i = -1) (hi_moved : star i ≠ i) :
    Nat.card (selfAdjoint k) ^ 2 = Nat.card k ∧ Nat.card (selfAdjoint k) % 4 = 3 := by
  -- `star i` is a square root of `-1` other than `i`, so it is `-i`, and `-i ≠ i` gives `2 ≠ 0`.
  have h_star : star i = -i := by grind [star_mul, star_neg, star_one, mul_self_eq_mul_self_iff]
  have h_two : (2 : k) ≠ 0 := by grind
  constructor
  · -- `(x, y) ↦ (x - i * y) / 2` is a bijection from pairs of fixed points onto `k`;
    -- its inverse sends `z` to the traces of `z` and of `i * z`.
    rw [sq, ← card_prod]
    refine card_congr
      { toFun := fun (x, y) ↦ (x - i * y) / 2
        invFun z := (⟨z + star z, .add_star_self z⟩, ⟨i * z + star (i * z), .add_star_self _⟩)
        left_inv := ?_
        right_inv z := by grind [star_mul'] }
    rintro ⟨⟨x, hx : star x = x⟩, ⟨y, hy : star y = y⟩⟩
    have h_conj : star ((x - i * y) / 2) = (x + i * y) / 2 := by simp [hx, hy, h_star]
    simp only [Prod.mk.injEq, Subtype.ext_iff]
    grind [star_mul']
  · -- `-1` is not a square in the field of fixed points: its square roots `±i` are moved.
    cases nonempty_fintype (selfAdjoint k)
    have h_not_square : ¬IsSquare (-1 : selfAdjoint k) := by
      rintro ⟨⟨x, hx : star x = x⟩, hx_sq⟩
      have hx_eq : x * x = i * i := by simpa [hi_sq, Subtype.ext_iff] using hx_sq.symm
      grind [mul_self_eq_mul_self_iff, star_neg]
    rwa [isSquare_neg_one_iff, not_not, Fintype.card_eq_nat_card] at h_not_square

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {w : FinPlace E}

/-- Let the CM field `E` contain an integer `β` with `β + β̄ = 1` and `β β̄` even. Then the places
above `2` are split: a finite place `w` fixed by conjugation does not lie above `2`. -/
lemma New.two_notMem_of_star_eq {β : 𝓞 E} (hβ : β + star β = 1) (h_even : 2 ∣ β * star β)
    (hw : star w = w) : 2 ∉ w.asIdeal := by
  -- If `2` lies in `w`, so does `β β̄`, hence both `β` and `β̄`; but their sum is `1`.
  intro h_two
  have h_star (x : 𝓞 E) : star x ∈ w.asIdeal ↔ x ∈ w.asIdeal := by rw [← mem_star_place, hw]
  have h_mem : β ∈ w.asIdeal :=
    (w.isPrime.mem_or_mem (w.asIdeal.mem_of_dvd h_even h_two)).elim id (h_star β).1
  exact w.isPrime.one_notMem (by simpa [hβ] using add_mem h_mem ((h_star β).2 h_mem))

/-- Let the CM field `E` contain an integer `i` with `i² = -1` and `ī = -i`, and an integer `β`
with `β + β̄ = 1` and `β β̄` even. If the finite place `w` is fixed by conjugation, its norm `w.q`,
the number of elements of its residue field, is `r²` with `r ≡ 3` modulo `4`. -/
lemma New.exists_sq_eq_q_of_star_eq {i β : 𝓞 E} (hi_sq : i * i = -1) (hi_star : star i = -i)
    (hβ : β + star β = 1) (h_even : 2 ∣ β * star β) (hw : star w = w) :
    ∃ r : ℕ, r ^ 2 = w.q ∧ r % 4 = 3 := by
  -- Conjugation descends to an involution of the residue field. It moves the image of `i`, because
  -- `w` does not lie over `2`; so `New.card_selfAdjoint` applies.
  let : Field (𝓞 E ⧸ w.asIdeal) := Quotient.field w.asIdeal
  let π : 𝓞 E →+* 𝓞 E ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
  let conj : 𝓞 E ⧸ w.asIdeal →+* 𝓞 E ⧸ w.asIdeal :=
    quotientMap w.asIdeal (starRingEnd (𝓞 E)) fun x hx ↦ mem_star_place.1 (by rwa [hw])
  let : StarRing (𝓞 E ⧸ w.asIdeal) := starRingOfInvolution conj <|
    Ideal.Quotient.mk_surjective.forall.2 fun x ↦ congrArg π (star_star x)
  have πi_sq : π i * π i = -1 := by simp [← map_mul, hi_sq]
  have two_ne : (2 : 𝓞 E ⧸ w.asIdeal) ≠ 0 := by
    simpa [← map_ofNat π 2, π, eq_zero_iff_mem] using two_notMem_of_star_eq hβ h_even hw
  have star_πi : star (π i) = -π i := (congrArg π hi_star).trans (map_neg π i)
  have star_πi_ne : star (π i) ≠ π i := by grind
  rw [FinPlace.q, absNorm_apply, Submodule.cardQuot_apply]
  exact ⟨Nat.card (selfAdjoint (𝓞 E ⧸ w.asIdeal)), card_selfAdjoint πi_sq star_πi_ne⟩

end

/-- In a CM field `E` only finitely many places of prime norm are fixed by complex conjugation. -/
lemma New.finite_prime_q_star_eq (E : Type*) [Field E] [NumberField E] [IsCMField E] :
    {w : FinPlace E | w.q.Prime ∧ star w = w}.Finite := by
  -- Such a place divides `y - ȳ` for every integer `y` of `E`, as `y` is congruent to a rational
  -- integer, and `y - ȳ ≠ 0` for some `y`.
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, y - star y ≠ 0 := by
    by_contra! h_fixed
    refine IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x ↦ ?_)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    have h_int (z : 𝓞 E) : IsCMField.complexConj E z = z :=
      congrArg (algebraMap (𝓞 E) E) (sub_eq_zero.1 (h_fixed z)).symm
    simp [h_int]
  have h_divisors : {w : FinPlace E | y - star y ∈ w.asIdeal}.Finite := by
    simp [← dvd_span_singleton, finite_factors, hy]
  refine h_divisors.subset fun w ⟨hq_prime, hw⟩ ↦ ?_
  have : Fact w.q.Prime := ⟨hq_prime⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • (1 : 𝓞 E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y :=
    mem_zmultiples_of_prime_card (p := w.q)
      (by rw [FinPlace.q, absNorm_apply, Submodule.cardQuot_apply]) one_ne_zero
  have h_mem : y - n ∈ w.asIdeal := Ideal.Quotient.eq.1 (by simp [← hn])
  have h_star_mem : star (y - n) ∈ w.asIdeal := mem_star_place.1 (by rwa [hw])
  simpa using w.asIdeal.sub_mem h_mem h_star_mem

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E]
  {w : FinPlace E}

/-- If the CM field `E` contains a primitive root of unity of order `5040`, a finite place above
`2` is split, that is, moved by complex conjugation. -/
lemma New.HasPrimitiveRoot5040.isSplit_of_two_mem (h_two : (2 : 𝓞 E) ∈ w.asIdeal) : w.IsSplit := by
  obtain ⟨-, ω, -, -, h_trace, h_norm⟩ := exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  exact fun hw : star w = w ↦ two_notMem_of_star_eq h_trace h_norm.symm.dvd hw h_two

/-- If the CM field `E` contains a primitive root of unity of order `5040`, the norm `w.q` of a
finite place `w` fixed by conjugation is `r²` with `r ≡ 3` modulo `4`. -/
lemma New.HasPrimitiveRoot5040.exists_sq_eq_q_of_inert (hw : star w = w) :
    ∃ r : ℕ, r ^ 2 = w.q ∧ r % 4 = 3 := by
  obtain ⟨i, ω, hi_sq, hi_star, h_trace, h_norm⟩ :=
    exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  exact exists_sq_eq_q_of_star_eq hi_sq hi_star h_trace h_norm.symm.dvd hw

/-- If the CM field `E` contains a primitive root of unity of order `5040`, a finite place whose
norm `w.q` (the number of elements of its residue field) is prime is split, that is, moved by
complex conjugation. -/
lemma New.isSplit_of_q_prime (hq_prime : w.q.Prime) : w.IsSplit := by
  -- If `w` were its own conjugate, the prime `w.q` would be a square.
  intro (hw : star w = w)
  obtain ⟨r, hr, -⟩ := exists_sq_eq_q_of_inert hw
  exact Nat.Prime.not_prime_pow le_rfl (by rwa [hr])

end InertResidue

/-! ## Frobenius on the roots of polynomials over a finite field -/

namespace New

open Polynomial FiniteField Nat Multiset

attribute [local instance low] Fintype.ofFinite

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]

@[simp]
lemma pow_pred_eq_one_iff {x : K} {Q : ℕ} (hQ : 2 ≤ Q) : x ^ (Q - 1) = 1 ↔ x ≠ 0 ∧ x ^ Q = x := by
  grind [pow_sub₀, zero_pow]

/-- The image in `K` of a unit of a finite field with `q` elements has `(q - 1)`-st power `1`. -/
@[simp]
lemma algebraMap_pow_card_pred_eq_one (a : kˣ) : algebraMap k K a ^ (Nat.card k - 1) = 1 := by
  simp [← map_pow, pow_card_sub_one_eq_one]

/-- Let `P` be irreducible over a finite field with `q` elements and `x` a root of `P` in `K`. Then
`x^(q^n) = x` iff the degree of `P` divides `n`. -/
lemma root_pow_card_pow_eq_self_iff {P : k[X]} (hP : Irreducible P) {x : K} (hx : aeval x P = 0)
    {n : ℕ} : x ^ Nat.card k ^ n = x ↔ P.natDegree ∣ n := by
  simp [hP.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← hP.dvd_iff_aeval_eq_zero hx, sub_eq_zero]

/-- Let `P` be irreducible over a finite field with `q` elements and `x` a root of `P` in `K`. Then
`x^(q^a) = x^(q^b)` iff `a ≡ b` modulo the degree of `P`. -/
lemma root_pow_card_pow_eq_iff_modEq {P : k[X]} (hP : Irreducible P) {x : K} (hx : aeval x P = 0)
    {a b : ℕ} : x ^ Nat.card k ^ a = x ^ Nat.card k ^ b ↔ a ≡ b [MOD P.natDegree] := by
  -- Frobenius is injective, so cancel it on both sides until one exponent is `0`; then this is
  -- `root_pow_card_pow_eq_self_iff`.
  have h_inj {u v : K} : u ^ Nat.card k = v ^ Nat.card k ↔ u = v := by
    simpa [coe_frobeniusAlgHom] using (frobeniusAlgHom k K).injective.eq_iff (a := u) (b := v)
  induction a, b using Nat.recDiagAux with
  | zero_left n =>
    simpa [eq_comm, modEq_iff_dvd' n.zero_le] using root_pow_card_pow_eq_self_iff hP hx
  | zero_right m => simpa [modEq_zero_iff_dvd] using root_pow_card_pow_eq_self_iff hP hx
  | succ_succ m n ih => simp only [pow_succ, pow_mul, h_inj, ih, ModEq.add_iff_right (.refl 1)]

/-- Let `P` be irreducible of degree `d` over a finite field with `q` elements and `x` a root of `P`
in `K`. The roots of `P` in `K`, with multiplicity, are `x, x^q, …, x^(q^(d-1))`. -/
lemma aroots_eq_frobenius_orbit {P : k[X]} (hP : Irreducible P) {x : K} (hx : aeval x P = 0) :
    P.aroots K = Multiset.map (fun i : ℕ ↦ x ^ Nat.card k ^ i) (range P.natDegree) := by
  -- The `x^(q^i)` are roots, being images of `x` under powers of Frobenius; those with `i < d` are
  -- distinct by `root_pow_card_pow_eq_iff_modEq`. So they are all the roots.
  have h_root (i : ℕ) : aeval (x ^ Nat.card k ^ i) P = 0 := by
    simpa [coe_frobeniusAlgHom, hx] using aeval_algHom_apply (frobeniusAlgHom k K ^ i) x P
  have h_nodup : ((range P.natDegree).map fun i : ℕ ↦ x ^ Nat.card k ^ i).Nodup :=
    (nodup_range P.natDegree).map_on fun a ha b hb h_eq ↦
      ((root_pow_card_pow_eq_iff_modEq hP hx).1 h_eq).eq_of_lt_of_lt (mem_range.1 ha)
        (mem_range.1 hb)
  have h_le : ((range P.natDegree).map fun i : ℕ ↦ x ^ Nat.card k ^ i) ≤ P.aroots K :=
    (le_iff_subset h_nodup).2 (by simpa [Multiset.subset_iff, hP.ne_zero] using fun i _ ↦ h_root i)
  exact (eq_of_le_of_card_le h_le (by simpa using card_roots' (P.map (algebraMap k K)))).symm

/-- With `q = |k|` and `x` a root in `K` of the irreducible `P`, the roots of `P ^ j` with
multiplicity are the `x ^ q ^ i` for `i < deg (P ^ j)`, and `x ^ q ^ deg (P ^ j) = x`. -/
lemma aroots_pow_eq_frobenius_orbit {P : k[X]} (hP : Irreducible P) {x : K} (hx : aeval x P = 0)
    {j : ℕ} :
    (P ^ j).aroots K = Multiset.map (fun i : ℕ ↦ x ^ Nat.card k ^ i) (range (P ^ j).natDegree) ∧
      x ^ Nat.card k ^ (P ^ j).natDegree = x := by
  -- The roots of `P` form one Frobenius orbit, which each further factor `P` repeats.
  have h_fixed (j : ℕ) : x ^ Nat.card k ^ (j * P.natDegree) = x :=
    (root_pow_card_pow_eq_self_iff hP hx).2 (dvd_mul_left P.natDegree j)
  rw [natDegree_pow]
  refine ⟨?_, h_fixed j⟩
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, aroots_mul (by simp [hP.ne_zero]), ih, aroots_eq_frobenius_orbit hP hx]
    simp only [add_one_mul, range_add, Multiset.map_add, Multiset.map_map, Function.comp_def,
      pow_add, pow_mul x, h_fixed]

/-- Let `P` be irreducible over a finite field with `q` elements and `x` a root of `P` in `K`. Every
root of `P` in `K` is `x^(q^i)` for some `i < deg P`. -/
lemma exists_pow_card_pow_eq_of_root {P : k[X]} (hP : Irreducible P) {x : K} (hx : aeval x P = 0)
    {y : K} (hy : aeval y P = 0) : ∃ i < P.natDegree, x ^ Nat.card k ^ i = y := by
  simpa [aroots_eq_frobenius_orbit hP hx] using mem_aroots.2 ⟨hP.ne_zero, hy⟩

end New

/-! ## Sums over `ℤ/N` for `N` prime -/

/-- For a prime modulus `N`, every nonzero element of `ℤ/N` is a unit, so a sum over `ℤ/N` is its
term at `0` plus the sum over the units. -/
lemma New.sum_eq_add_sum_units {N : ℕ} [Fact N.Prime] {V : Type*} [AddCommMonoid V]
    (f : ZMod N → V) : ∑ c : ZMod N, f c = f 0 + ∑ c : (ZMod N)ˣ, f c.val := by
  simp [Fintype.sum_eq_add_sum_subtype_ne f 0, ← unitsEquivNeZero.sum_comp]
