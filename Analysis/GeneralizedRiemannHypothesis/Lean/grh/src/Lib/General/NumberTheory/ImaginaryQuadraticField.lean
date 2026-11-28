import Lib.General.NumberTheory.EmbeddingsAndDifferent

/-!
# The imaginary quadratic field ℚ(√−d): characters, Frobenius and splitting of primes

This file studies the imaginary quadratic field `K = ℚ(√-d)` (`New.QuadField`) for `d ≡ 3 mod 4`,
realised inside `ℂ`, and the Dirichlet characters attached to it. Throughout, `New.chiK d p` is the
Legendre symbol `(p / d)` of `p` modulo the prime `d`, and `New.QuadField.betaK d` is the algebraic
integer `(1 + √-d) / 2`. A finite place of `K` (`New.FinPlace`) is a nonzero prime of its ring of
integers. Below, `w` is a finite place that contains the rational prime `p`, and `w.q` is its
absolute norm. For a prime `d ≡ 7 mod 8` the file determines the ring of integers and the different
of `K`. For `d ≡ 3 mod 4` it shows how a rational prime `p` decomposes in `K`. It also proves two
consequences of lifting the exponent at `2` for integers, which do not involve `K`.

## Main definitions and results

* `New.chiK`, `New.quadTwist`: the Legendre symbol `(·/d)` as an integer-valued character, and its
  product with a complex character `χ` modulo `N`, a character modulo `N * d`.
* `New.QuadField`: the field. For `d ≡ 3` modulo `4` it is a quadratic CM field
  (the degree is `New.QuadField.finrank_eq_two`). For a prime `d ≡ 3` modulo `4` it embeds in any
  field of characteristic zero with a primitive `d`-th root of unity
  (`New.QuadField.embOfPrimitiveRoot`).
* `New.QuadField.different_eq_span_and_adjoin_betaK`: for a prime `d ≡ 7` modulo `8`, the integers
  of `K` are `ℤ[(1 + √-d) / 2]` and the different is `(√-d)`.
* `New.FinPlace.q_eq_pow_inertiaDeg`, `New.FinPlace.inertiaDeg_dvd_iff_forall_pow_eq`: the norm of
  `w` is `p ^ f` with `f` the residue degree, and `f` is the order of Frobenius;
  `New.FinPlace.exists_q_eq_pow` states both together.
* `New.QuadField.q_eq_iff_chiK_ne_neg_one`: for `d` a prime `≡ 7 mod 8`
  (`New.PrimeSevenModEight`), `w` has degree one iff the Legendre symbol `(p / d)` is not `-1`.
* `New.QuadField.span_eq_or_exists_span_eq_mul`: `p` is inert in `K`, or it is the product of two
  places of degree one; `New.QuadField.prime_inert_or_eq_mul` also lists the places above `p`.
-/

noncomputable section

/-!
## The field ℚ(√−d), its quadratic character and its ring of integers

`star` on `K` and on its integers is complex conjugation.
-/

section QuadField

open NumberField Complex Polynomial InfinitePlace Module IntermediateField AddChar

namespace New

instance (d : Nat.Primes) : Fact d.val.Prime := ⟨d.prop⟩

section Characters

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-! ### Characters and `L`-functions -/

/-- For a prime d, the Legendre symbol (·/d) as an integer-valued Dirichlet character modulo d; for
d ≡ 3 mod 4 it is the character χ_K of K = ℚ(√−d). -/
def chiK : DirichletCharacter ℤ d := quadraticChar (ZMod d)

lemma chiK_eq_legendreSym (n : ℕ) : chiK d n = legendreSym d n := by simp [chiK, legendreSym]

/-- The product of `χ`, a character modulo `N`, and the Legendre symbol `(·/d)`, as a character
modulo `N * d`. -/
def quadTwist : DirichletCharacter ℂ (N * d) :=
  χ.changeLevel ⟨d, rfl⟩ * .changeLevel (by simp) ((chiK d).ringHomComp (algebraMap ℤ ℂ))

/-- The entire function equal to L(s, χ) if χ is not principal, and to the continuation of
(s − 1)L(s, χ) if χ is principal. -/
def entireL : ℂ → ℂ := if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ N else χ.LFunction

/-- The real number `γ - Re L'/L(1, χ_K)`, with `γ` Euler's constant. The character is written as
the twist by `(·/d)` of the character modulo `1`, which for `d ≡ 3 mod 4` is `χ_K` at level
`1 * d`. For odd `d` it is not principal, so `New.entireL` of it is its `L`-function. -/
def chowlaSelbergConst : ℝ :=
  Real.eulerMascheroniConstant - (logDeriv (entireL (quadTwist (N := 1) 1 d)) 1).re
end Characters

/-- If a number field `M` contains primitive roots of unity of coprime orders `n` and `d`, then its
degree over `ℚ` is at least `φ(d) φ(n)`. -/
lemma totient_mul_totient_le_finrank (d n : ℕ) [NeZero n] {M : Type} [Field M] [CharZero M]
    {x y : M} [NeZero d] [NumberField M] (h_cop : n.Coprime d) (hx : IsPrimitiveRoot x n)
    (hy : IsPrimitiveRoot y d) :
    d.totient * n.totient ≤ finrank ℚ M := by
  rw [mul_comm, ← Nat.totient_mul h_cop, ← h_cop.lcm_eq_mul]
  exact hx.lcm_totient_le_finrank hy (cyclotomic.irreducible_rat (by simp [NeZero.pos]))

variable (d : ℕ)

/-! ### The field `K = ℚ(√-d)` -/

/-- The natural number d is a prime congruent to 7 modulo 8. -/
class PrimeSevenModEight extends Fact d.Prime where
  /-- `d ≡ 7` modulo `8`. -/
  mod_eight : d % 8 = 7

/-- The subfield K = ℚ(i√d) of ℂ. -/
def QuadField : IntermediateField ℚ ℂ := ℚ⟮I * √d⟯

namespace QuadField

/-- The generator √−d = i√d of K = ℚ(i√d). -/
@[simps! coe]
def sqrtNegD : QuadField d := AdjoinSimple.gen ℚ (I * √d)

@[local simp]
lemma sqrtNegD_sq : sqrtNegD d ^ 2 = -d := by
  ext
  simp [mul_pow, ← ofReal_pow]

lemma isIntegral_I_mul_sqrt : IsIntegral ℚ (I * (√d : ℂ)) :=
  .of_pow two_pos (by simp [isIntegral_natCast, mul_pow, ← ofReal_pow])

instance : NumberField (QuadField d) where
  to_finiteDimensional := adjoin.finiteDimensional (isIntegral_I_mul_sqrt d)

instance [PrimeSevenModEight d] : Fact (d % 4 = 3) := ⟨by grind [PrimeSevenModEight]⟩

variable [h : Fact (d % 4 = 3)]

instance : NeZero d := ⟨by grind [Fact]⟩

/-- For `d ≡ 3 mod 4`, the minimal polynomial of `i√d` over `ℚ` is `X ^ 2 + d`. -/
lemma minpoly_I_mul_sqrt : X ^ 2 - C (-d : ℚ) = minpoly ℚ (I * (√d : ℂ)) := by
  have h_irred : Irreducible (X ^ 2 - C (-d : ℚ)) := by
    -- `-d` is negative, hence not a square in `ℚ`
    refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb ↦ ?_
    simpa [hb, NeZero.ne] using sq_nonneg b
  exact minpoly.eq_of_irreducible_of_monic h_irred (by simp [mul_pow, ← ofReal_pow]) (by monicity!)

/-- For `d ≡ 3 mod 4`, the field `K = ℚ(√-d)` has degree `2` over `ℚ`. -/
lemma finrank_eq_two : finrank ℚ (QuadField d) = 2 := by
  rw [QuadField, adjoin.finrank (isIntegral_I_mul_sqrt d), ← minpoly_I_mul_sqrt]
  compute_degree!

instance : IsTotallyComplex (QuadField d) := by
  -- a real embedding would give `-d` a real square root
  refine ⟨fun w ↦ not_isReal_iff_isComplex.mp fun hw ↦ ?_⟩
  simpa [← map_pow, NeZero.ne] using sq_nonneg (embedding_of_isReal hw (sqrtNegD d))

instance : Unique (InfinitePlace (QuadField d)) where
  default := mk (val (QuadField d)).toRingHom
  -- `K` is totally complex of degree `2`, so it has one infinite place
  uniq w := Fintype.card_le_one_iff.mp
    (by grind [finrank_eq_two_mul_card_infinitePlace, finrank_eq_two]) w _

/-- For d ≡ 3 mod 4 and y with y² = −d in a field M of characteristic zero, the embedding of
K = ℚ(i√d) into M sending i√d to y. -/
def embOfSqrt (d : ℕ) {M : Type} [Field M] [CharZero M] {y : M} [h : Fact (d % 4 = 3)]
    (e : y ^ 2 = -d) : QuadField d →ₐ[ℚ] M :=
  (adjoin.powerBasis (isIntegral_I_mul_sqrt d)).lift y
    (by simp [minpoly_gen, ← minpoly_I_mul_sqrt, e])

open Subalgebra Int Algebra Ideal ZMod

/-- For a prime d ≡ 3 mod 4, an embedding of ℚ(√−d) in a field M of characteristic zero that
contains a primitive d-th root of unity, given by the quadratic Gauss sum. -/
def embOfPrimitiveRoot (d : ℕ) {M : Type} [Field M] [CharZero M] {x : M} [h : Fact (d % 4 = 3)]
    [Fact d.Prime] (hx : IsPrimitiveRoot x d) : QuadField d →ₐ[ℚ] M :=
  embOfSqrt d <| by
    -- the square of the quadratic Gauss sum is `χ(-1) d`, and `χ(-1) = -1` as `d ≡ 3` mod `4`
    have h_neg_one : quadraticChar (ZMod d) (-1) = -1 := by
      simp [quadraticCharFun, exists_sq_eq_neg_one_iff, (Fact.out : d % 4 = 3)]
    have h_ne_one : (quadraticChar (ZMod d)).ringHomComp (castRingHom M) ≠ 1 :=
      MulChar.ne_one_iff.2 ⟨-1, by simp [h_neg_one, neg_eq_self]⟩
    rw [gaussSum_sq h_ne_one ((quadraticChar_isQuadratic _).comp (castRingHom M))
      (zmodChar_primitive_of_primitive_root d hx)]
    simp [h_neg_one]

/-- For `d ≡ 3 mod 4`, `4` divides `d + 1`. -/
@[simp]
lemma four_dvd_d_add_one : 4 ∣ d + 1 := by grind [Fact]

instance : IsQuadraticExtension ℚ (QuadField d) := ⟨finrank_eq_two d⟩

instance : IsCMField (QuadField d) := .ofCMExtension ℚ _

@[simp]
lemma coe_star_eq_conj (y : QuadField d) : ((star y : QuadField d) : ℂ) = starRingEnd ℂ (y : ℂ) :=
  map_star_complex (QuadField d).val y

@[simp]
lemma star_sqrtNegD : star (sqrtNegD d) = -sqrtNegD d := by
  ext
  simp

/-- For d ≡ 3 mod 4, the absolute value of the norm of x ∈ K ⊂ ℂ is |x|², as K has a single,
complex, infinite place. -/
lemma abs_norm_eq_norm_sq (x : QuadField d) : |(Algebra.norm ℚ x : ℝ)| = ‖(x : ℂ)‖ ^ 2 := by
  simpa [show (default : InfinitePlace (QuadField d)) x = ‖x.val‖ from rfl] using
    (prod_eq_abs_norm x).symm

/-- For `d ≡ 3 mod 4`, the absolute norm of the ideal generated by an integer `y` of `K = ℚ(√-d)`
is `y * ȳ`, where `star y = ȳ` is the complex conjugate of `y`. -/
lemma absNorm_span_eq_mul_star (y : 𝓞 (QuadField d)) :
    ((span {y}).absNorm : 𝓞 (QuadField d)) = y * star y := by
  -- The map to ℂ is injective, and both sides are `|y| ^ 2` there.
  have h_norm : ((span {y}).absNorm : ℝ) = ‖((y : QuadField d) : ℂ)‖ ^ 2 := by
    rw [← abs_norm_eq_norm_sq, ← coe_norm_int]
    simp [cast_abs]
  ext
  -- `cast_abs` is left out: it moves the absolute value on one side only
  simp [mul_conj', ← ofReal_pow, ← h_norm, -cast_abs]

/-! ### The ring of integers of `K` -/

/-- For d ≡ 3 mod 4, the algebraic integer (1 + √−d)/2 of K = ℚ(√−d). -/
def betaK : 𝓞 (QuadField d) where
  val := (1 + sqrtNegD d) / 2
  -- a root of the monic integral polynomial `X ^ 2 - X + (d + 1) / 4`, as `sqrtNegD d ^ 2 = -d`
  property := by
    refine ⟨X ^ 2 - X + ((d + 1) / 4).cast, by monicity!, ?_⟩
    simp
    grind [sqrtNegD_sq]

@[simp]
lemma coe_betaK : (betaK d : QuadField d) = (1 + sqrtNegD d) / 2 := rfl

@[simp]
lemma star_betaK : star (betaK d) = 1 - betaK d := by
  suffices (1 + -sqrtNegD d) / 2 = 1 - (1 + sqrtNegD d) / 2 by simpa [RingOfIntegers.ext_iff]
  ring

/-- For `d ≡ 3 mod 4`, the element `betaK d = (1 + √-d) / 2` times its conjugate `1 - betaK d` is
the natural number `(d + 1) / 4`. The division is exact, as `4` divides `d + 1`. -/
lemma betaK_mul_one_sub : betaK d * (1 - betaK d) = (((d + 1) / 4 : ℕ) : 𝓞 (QuadField d)) := by
  suffices (1 + sqrtNegD d) / 2 * (1 - (1 + sqrtNegD d) / 2) = ((d : QuadField d) + 1) / 4 by
    simpa [RingOfIntegers.ext_iff]
  grind [sqrtNegD_sq]

/-- For d ≡ 3 mod 4, the element √−d = i√d of the ring of integers of K = ℚ(√−d), defined as
2·(1 + √−d)/2 − 1. -/
abbrev sqrtNegDInt : 𝓞 (QuadField d) := 2 * betaK d - 1

/-- For `d ≡ 3 mod 4`, the square of the algebraic integer `√-d = 2 * betaK d - 1` is `-d`. -/
lemma sqrtNegDInt_sq : sqrtNegDInt d ^ 2 = -d := by simp [two_mul, RingOfIntegers.ext_iff]

/-- For a prime `d ≡ 7` modulo `8`, the different ideal of the ring of integers of `K = ℚ(√-d)`
over `ℤ` is generated by `sqrtNegDInt d = 2 * betaK d - 1 = √-d`, and the subring `ℤ[betaK d]` is
the whole ring of integers of `K`, where `betaK d = (1 + √-d) / 2`. -/
lemma different_eq_span_and_adjoin_betaK [PrimeSevenModEight d] :
    differentIdeal ℤ (𝓞 (QuadField d)) = span {sqrtNegDInt d} ∧ ℤ[betaK d] = ⊤ := by
  -- `betaK d` is not rational (twice it has imaginary part `√d`), and `K` has degree `2`.
  have adjoin_eq_top : ℚ[(betaK d : QuadField d)] = ⊤ := by
    have : IsSimpleOrder (Subalgebra ℚ (QuadField d)) := isSimpleOrder_of_finrank (finrank_eq_two d)
    refine (eq_bot_or_eq_top _).resolve_left fun h_bot ↦ ?_
    obtain ⟨x, hx⟩ := Algebra.mem_bot.1 (h_bot.le (subset_adjoin (Set.mem_singleton _)))
    have h_double : algebraMap ℚ (QuadField d) (x + x) = 1 + sqrtNegD d := by simp [map_add, hx]
    have h_complex : (x : ℂ) + x = 1 + I * √d := by simpa using congrArg Subtype.val h_double
    simpa [NeZero.ne] using (congrArg Complex.im h_complex).symm
  -- `betaK d` is a root of `f = X ^ 2 - X + (d + 1) / 4`, and `f'(betaK d) = 2 * betaK d - 1 = √-d`
  -- divides the different, as its square is `-d` with `d` prime. As `betaK d` generates `K`, it
  -- follows that it generates the ring of integers (`differentIdeal_eq_span_of_dvd`).
  have h_mem : (d : 𝓞 (QuadField d)) ∈ span {sqrtNegDInt d} ^ 2 := by
    simp [span_singleton_pow, sqrtNegDInt_sq]
  let f : ℤ[X] := X ^ 2 - X + (((d + 1) / 4 : ℕ) : ℤ[X])
  have hf_root : aeval (betaK d) f = 0 := by
    simp only [f, map_add, map_sub, map_pow, aeval_X, map_natCast]
    linear_combination -betaK_mul_one_sub d
  have hf_derivative : aeval (betaK d) f.derivative = sqrtNegDInt d := by simp [f, map_ofNat]
  exact differentIdeal_eq_span_of_dvd ℚ adjoin_eq_top f hf_root hf_derivative
    (dvd_differentIdeal_of_mem_sq h_mem)

end QuadField

end New

end QuadField

/-! ## Residue degrees, Frobenius, and 2-adic lifting the exponent -/

section PrimesInK

open NumberField Ideal Ideal.Quotient FiniteField legendreSym CharP ZMod Int

attribute [local instance] Quotient.field ZMod.algebra

namespace New

variable (F : Type*) [Field F] [NumberField F] (d p : ℕ) [hp : Fact p.Prime]

namespace FinPlace

/-! ### Primes above a rational prime -/

/-- Every rational prime `p` lies in some finite place of the number field `F`. -/
lemma exists_natCast_mem : ∃ w : FinPlace F, (p : 𝓞 F) ∈ w.asIdeal := by
  obtain ⟨P, hP, ⟨h_over⟩⟩ : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 F)) :=
    nonempty_primesOver _
  -- A prime ideal over `(p)` is non-zero because `p ≠ 0`.
  exact ⟨⟨P, hP, fun h_bot ↦ by simp [h_bot, NeZero.ne] at h_over⟩, by simpa using h_over.le⟩

variable {F p} (w : FinPlace F)

lemma charP_quotient (hw : (p : 𝓞 F) ∈ w.asIdeal) : CharP (𝓞 F ⧸ w.asIdeal) p :=
  (CharP.charP_iff_prime_eq_zero hp.1).2 (eq_zero_iff_mem.2 hw)

protected lemma natCast_mem_iff_dvd (hw : (p : 𝓞 F) ∈ w.asIdeal) {n : ℕ} :
    (n : 𝓞 F) ∈ w.asIdeal ↔ p ∣ n := by
  rw [← (w.charP_quotient hw).cast_eq_zero_iff, ← map_natCast (Ideal.Quotient.mk _),
    eq_zero_iff_mem]

/-- If the finite place `w` lies above the prime `p`, its absolute norm `w.q` is `p ^ f`, where
`f = w.asIdeal.inertiaDeg ℤ` is the residue degree of `w`. -/
lemma q_eq_pow_inertiaDeg (hw : (p : 𝓞 F) ∈ w.asIdeal) : w.q = p ^ w.asIdeal.inertiaDeg ℤ := by
  have : w.asIdeal.LiesOver (span {(p : ℤ)}) :=
    (liesOver_span_iff w.isPrime.ne_top (Nat.prime_iff_prime_int.1 hp.1)).2 (by simpa using hw)
  exact (pow_inertiaDeg p w.asIdeal).symm

/-- The residue degree is the order of Frobenius: if the finite place `w` lies above the prime `p`,
then `x ↦ x ^ p ^ n` is the identity modulo `w` exactly when the residue degree of `w` divides
`n`. -/
lemma inertiaDeg_dvd_iff_forall_pow_eq (hw : (p : 𝓞 F) ∈ w.asIdeal) (n : ℕ) :
    w.asIdeal.inertiaDeg ℤ ∣ n ↔
      ∀ x : 𝓞 F, Ideal.Quotient.mk w.asIdeal x ^ p ^ n = Ideal.Quotient.mk w.asIdeal x := by
  have : CharP (𝓞 F ⧸ w.asIdeal) p := w.charP_quotient hw
  -- The residue field has `p ^ f` elements, so `f` is its degree over `ZMod p`.
  have h_norm : w.q = p ^ Module.finrank (ZMod p) (𝓞 F ⧸ w.asIdeal) := by
    rw [pow_finrank_eq_natCard p, FinPlace.q, absNorm_apply, Submodule.cardQuot_apply]
  have h_degree : w.asIdeal.inertiaDeg ℤ = Module.finrank (ZMod p) (𝓞 F ⧸ w.asIdeal) :=
    Nat.pow_right_injective hp.1.two_le ((w.q_eq_pow_inertiaDeg hw).symm.trans h_norm)
  calc
    w.asIdeal.inertiaDeg ℤ ∣ n ↔ frobeniusAlgHom (ZMod p) (𝓞 F ⧸ w.asIdeal) ^ n = 1 := by
      rw [h_degree, ← orderOf_frobeniusAlgHom, orderOf_dvd_iff_pow_eq_one]
    _ ↔ ∀ x : 𝓞 F, Ideal.Quotient.mk w.asIdeal x ^ p ^ n = Ideal.Quotient.mk w.asIdeal x := by
      simp [AlgHom.ext_iff, mk_surjective.forall, coe_frobeniusAlgHom]

/-- If the finite place `w` lies above the prime `p`, there is an `f` such that the absolute norm
`w.q` is `p ^ f` and `x ↦ x ^ p ^ n` is the identity modulo `w` exactly when `f ∣ n`. This `f` is
the residue degree of `w`. -/
lemma exists_q_eq_pow (hw : (p : 𝓞 F) ∈ w.asIdeal) :
    ∃ f : ℕ,
      w.q = p ^ f ∧
      ∀ n : ℕ,
        f ∣ n ↔
          ∀ x : 𝓞 F, Ideal.Quotient.mk w.asIdeal x ^ p ^ n = Ideal.Quotient.mk w.asIdeal x :=
  ⟨w.asIdeal.inertiaDeg ℤ, w.q_eq_pow_inertiaDeg hw, w.inertiaDeg_dvd_iff_forall_pow_eq hw⟩

/-- If `(a) = w`, then `w` is the only finite place that contains `a`. -/
lemma mem_asIdeal_iff_of_span_eq {a : 𝓞 F} (h_span : span {a} = w.asIdeal) (u : FinPlace F) :
    a ∈ u.asIdeal ↔ u = w := by
  rw [← dvd_span_singleton, h_span, prime_dvd_prime_iff_eq u.prime w.prime,
    IsDedekindDomain.HeightOneSpectrum.ext_iff]

/-- If `(a) = w w'`, then the finite places that contain `a` are `w` and `w'`. -/
lemma mem_asIdeal_iff_of_span_eq_mul {w' : FinPlace F} {a : 𝓞 F}
    (h_span : span {a} = w.asIdeal * w'.asIdeal) (u : FinPlace F) :
    a ∈ u.asIdeal ↔ u = w ∨ u = w' := by
  rw [← dvd_span_singleton, h_span, u.prime.dvd_mul, prime_dvd_prime_iff_eq u.prime w.prime,
    prime_dvd_prime_iff_eq u.prime w'.prime, IsDedekindDomain.HeightOneSpectrum.ext_iff,
    IsDedekindDomain.HeightOneSpectrum.ext_iff]

end FinPlace

namespace QuadField

variable {d p} {R : Type*} [CommRing R] [CharP R p] [PrimeSevenModEight d]

/-! ### Frobenius on `√-d` -/

/-- For a prime `d ≡ 7 mod 8`, a ring map from the integers of `ℚ(√-d)` to a commutative ring sends
`√-d = 2 * betaK d - 1` to a square root of `-d`. -/
lemma map_sqrtNegDInt_sq (φ : 𝓞 (QuadField d) →+* R) : φ (sqrtNegDInt d) ^ 2 = -d := by
  rw [← map_pow, sqrtNegDInt_sq, map_neg, map_natCast]

/-- For a prime `d ≡ 7 mod 8`, the Legendre symbol `chiK d 2 = (2 / d)` is `1`. -/
lemma chiK_two {d : ℕ} [PrimeSevenModEight d] : chiK d 2 = 1 := by
  have h_mod : d % 8 = 7 := PrimeSevenModEight.mod_eight
  -- The second supplement to quadratic reciprocity: `(2 / d) = χ₈ d` for odd `d`.
  calc
    chiK d 2 = legendreSym d 2 := by simpa using chiK_eq_legendreSym d 2
    _ = χ₈ d := at_two (by omega)
    _ = 1 := by rw [χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega), ite_eq_left (.inr h_mod)]

/-- For a prime `d ≡ 7 mod 8`, an odd prime `p` and a square root `x` of `-d` in a ring `R` of
characteristic `p`, `x ^ (p - 1)` is the image in `R` of the Legendre symbol `(p / d)`. -/
lemma chiK_eq_pow_of_sq_eq_neg (hp_ne_two : p ≠ 2) {x : R} (hx : x ^ 2 = -d) :
    chiK d p = x ^ (p - 1) := by
  -- Quadratic reciprocity and Euler's criterion give `(-d) ^ (p / 2)`, which is `x ^ (p - 1)`.
  have hd_half : Odd (d / 2) := by grind [PrimeSevenModEight]
  have hp_half : p - 1 = 2 * (p / 2) := by grind [hp.1.odd_of_ne_two hp_ne_two]
  -- The sign `(-1) ^ (p / 2 * (d / 2))` is `(-1) ^ (p / 2)` because `d / 2` is odd.
  have h_recip : chiK d p = (-1) ^ (p / 2) * legendreSym p d := by
    simp [chiK_eq_legendreSym,
      quadratic_reciprocity' hp_ne_two (show d ≠ 2 by grind [PrimeSevenModEight]),
      neg_one_pow_eq_ite, Nat.even_mul, Nat.not_even_iff_odd.2 hd_half]
  have h_euler : (legendreSym p d : R) = d ^ (p / 2) := by
    simpa using congr_arg (castHom (dvd_refl p) R) (eq_pow p d)
  rw [hp_half, pow_mul, hx, neg_pow (d : R)]
  simp [h_recip, h_euler]

/-- For a prime `d ≡ 7 mod 8`, an odd prime `p` and a ring map `φ` from the integers of `ℚ(√-d)`
to a ring of characteristic `p`, the `n`-th power of Frobenius sends `φ (betaK d)` to the `x` with
`2 x - 1 = (p / d) ^ n φ (√-d)`. Here `betaK d = (1 + √-d) / 2`,
`sqrtNegDInt d = √-d = 2 * betaK d - 1` and `chiK d p` is the Legendre symbol `(p / d)`. -/
lemma eq_map_betaK_pow_iff (hp_ne_two : p ≠ 2) (φ : 𝓞 (QuadField d) →+* R) (n : ℕ) (x : R) :
    x = φ (betaK d) ^ p ^ n ↔ 2 * x - 1 = chiK d p ^ n * φ (sqrtNegDInt d) := by
  -- Frobenius multiplies the square root `φ (sqrtNegDInt d)` of `-d` by `chiK d p`.
  have h_frob : φ (sqrtNegDInt d) ^ p = chiK d p * φ (sqrtNegDInt d) := by
    rw [chiK_eq_pow_of_sq_eq_neg hp_ne_two (map_sqrtNegDInt_sq φ), pow_sub_one_mul hp.1.ne_zero]
  have h_iter : φ (sqrtNegDInt d) ^ p ^ n = chiK d p ^ n * φ (sqrtNegDInt d) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        φ (sqrtNegDInt d) ^ p ^ (n + 1)
        _ = (chiK d p ^ n * φ (sqrtNegDInt d) : R) ^ p := by rw [pow_succ, pow_mul, ih]
        _ = frobenius R p (chiK d p ^ n) * φ (sqrtNegDInt d) ^ p := by rw [mul_pow, frobenius_def]
        _ = chiK d p ^ (n + 1) * φ (sqrtNegDInt d) := by
          rw [map_pow, map_intCast, h_frob, ← mul_assoc, ← pow_succ]
  -- Frobenius is a ring map, and `2` is a unit as `p` is odd.
  have h_add : φ (sqrtNegDInt d) ^ p ^ n = 2 * φ (betaK d) ^ p ^ n - 1 := by
    simp [← iterateFrobenius_def, map_ofNat]
  have h_unit : IsUnit (2 : R) := by
    simp [isUnit_ofNat_iff, p.prime_dvd_prime_iff_eq, Fact.out, hp_ne_two]
  rw [← h_iter, h_add, sub_left_inj, h_unit.mul_right_inj]

end QuadField

/-! ### The norm `q` and the values of the Legendre symbol -/

variable [Fact d.Prime]

/-- The number q: p² if (p/d) = −1, and p otherwise. For primes p and d ≡ 7 mod 8 it is the norm of
a prime of ℚ(√−d) above p. -/
abbrev primeNorm : ℕ := if chiK d p = -1 then p ^ 2 else p

/-- For primes `p` and `d`, the Legendre symbol `chiK d p = (p / d)` is `0` if `p = d`, and it is
`1` or `-1` otherwise. -/
lemma chiK_cases (d p : ℕ) [hp : Fact p.Prime] [Fact d.Prime] :
    p = d ∧ chiK d p = 0 ∨ p ≠ d ∧ (chiK d p = 1 ∨ chiK d p = -1) := by
  obtain rfl | hne := eq_or_ne p d
  · exact .inl ⟨rfl, by rw [chiK, natCast_self, quadraticChar_apply, quadraticCharFun_zero]⟩
  · exact .inr ⟨hne, quadraticChar_dichotomy (prime_ne_zero d p hne.symm)⟩

/-! ### Lifting the exponent at `2` -/

/-- If `q ^ o ≡ 1 mod 2 ^ (s + 1)` and `o ≠ 0`, then `2 ^ s` divides `(q - 1) o` or `(q + 1) o`.
This follows from lifting the exponent at `2`. -/
lemma two_pow_dvd_or_of_pow_eq_one {q : ℤ} {o s : ℕ} (ho : 0 < o)
    (h_pow : (q : ZMod (2 ^ (s + 1))) ^ o = 1) : 2 ^ s ∣ (q - 1) * o ∨ 2 ^ s ∣ (q + 1) * o := by
  -- Let `e = ±1` be congruent to `q` modulo `4`. Lifting the exponent for `q ^ (2 o) - e ^ (2 o)`
  -- gives `s + 1 ≤ v₂ (q - e) + v₂ o + 1`.
  have h_dvd : (2 : ℤ) ^ (s + 1) ∣ q ^ (o * 2) - 1 :=
    (intCast_eq_intCast_iff_dvd_sub 1 (q ^ (o * 2)) (2 ^ (s + 1))).1 (by simp [h_pow, pow_mul])
  have h_odd : Odd q := by
    simpa [coe_int_isUnit_iff_isCoprime, IsCoprime.pow_left_iff] using
      IsUnit.of_pow_eq_one h_pow ho.ne'
  have lte {e : ℤ} (he : e ^ (o * 2) = 1) (h_four : 4 ∣ q - e) : 2 ^ s ∣ (q - e) * o := by
    have h_lte : emultiplicity 2 (q ^ (o * 2) - e ^ (o * 2)) =
        emultiplicity 2 (q - e) + emultiplicity (2 : ℤ) ((o * 2 : ℕ) : ℤ) :=
      Int.two_pow_sub_pow' (o * 2) h_four (by grind)
    have h_two : emultiplicity (2 : ℤ) ((o * 2 : ℕ) : ℤ) = emultiplicity 2 (o : ℤ) + 1 := by
      simp [emultiplicity_mul Int.prime_two, Int.finiteMultiplicity_iff]
    have h_le : ((s + 1 : ℕ) : ℕ∞) ≤ emultiplicity 2 ((q - e) * o) + 1 := by
      rw [emultiplicity_mul Int.prime_two, add_assoc, ← h_two, ← h_lte, he]
      exact pow_dvd_iff_le_emultiplicity.1 h_dvd
    rw [pow_dvd_iff_le_emultiplicity]
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (by simpa using h_le)
  obtain h_four | h_four : 4 ∣ q - 1 ∨ 4 ∣ q - -1 := by grind
  · exact .inl (lte (one_pow _) h_four)
  · exact .inr (by simpa using lte (by simp) h_four)

/-- If q is an integer with |q| > 1, o is a nonzero natural number and q^o ≡ 1 mod 2^(s+1), then
2^s ≤ (|q| + 1)·o.

A consequence of the lifting-the-exponent lemma at the prime 2. It gives a lower bound for the
multiplicative order of q modulo 2^(s+1). -/
lemma two_pow_le_of_pow_eq_one {q : ℤ} (hq_one : 1 < q.natAbs) {o s : ℕ} (ho : 0 < o)
    (h_pow : (q : ZMod (2 ^ (s + 1))) ^ o = 1) : 2 ^ s ≤ (q.natAbs + 1) * o := by
  -- `2 ^ s` divides the non-zero integer `(q ∓ 1) * o`, and `|q ∓ 1| ≤ |q| + 1`.
  have key {x : ℤ} (hx : x ≠ 0) (hx_le : |x| ≤ |q| + 1) (h_dvd : 2 ^ s ∣ x * o) :
      2 ^ s ≤ (|q| + 1) * o := calc
    (2 : ℤ) ^ s ≤ |x * o| := Int.le_abs_of_dvd (by simp [hx, ho.ne']) h_dvd
    _ = |x| * o := by rw [abs_mul, Nat.abs_cast]
    _ ≤ (|q| + 1) * o := by gcongr
  zify
  obtain h_dvd | h_dvd := two_pow_dvd_or_of_pow_eq_one ho h_pow
  · exact key (x := q - 1) (by grind) (by grind) h_dvd
  · exact key (x := q + 1) (by grind) (by grind) h_dvd

end New

end PrimesInK

/-! ## Decomposition of rational primes in K -/

section QuadFieldSplitting

open Ideal IsDedekindDomain HeightOneSpectrum Quotient
open scoped NumberField

namespace New.QuadField

variable {d p : ℕ} [Fact (d % 4 = 3)] [hp : Fact p.Prime] (w : FinPlace (QuadField d))

/-- Let `d` be a prime `≡ 7 mod 8` and `w` a prime of `K = ℚ(√-d)` above the rational prime `p`.
Then the absolute norm `w.q` of `w` is `p` if and only if the Legendre symbol
`chiK d p = (p / d)` is not `-1`. -/
lemma q_eq_iff_chiK_ne_neg_one (hw : (p : 𝓞 (QuadField d)) ∈ w.asIdeal) [PrimeSevenModEight d] :
    w.q = p ↔ chiK d p ≠ -1 := by
  have char_p : CharP (𝓞 (QuadField d) ⧸ w.asIdeal) p := w.charP_quotient hw
  set π : 𝓞 (QuadField d) →+* 𝓞 (QuadField d) ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
  -- `w.q = p ^ f`, and the residue degree `f` is the order of Frobenius on the residue field.
  have q_iff_frob : w.q = p ↔ ∀ x : 𝓞 (QuadField d), π x ^ p ^ 1 = π x := by
    rw [w.q_eq_pow_inertiaDeg hw, ← w.inertiaDeg_dvd_iff_forall_pow_eq hw 1]
    simp [hp.1.pow_eq_iff]
  -- Frobenius is a ring map and `betaK d` generates the ring of integers.
  have frob_iff :
      (∀ x : 𝓞 (QuadField d), π x ^ p ^ 1 = π x) ↔ π (betaK d) ^ p ^ 1 = π (betaK d) := by
    refine ⟨fun h_all ↦ h_all (betaK d), fun h_gen x ↦ ?_⟩
    have hx : x ∈ Algebra.adjoin ℤ {betaK d} := by
      simp [(different_eq_span_and_adjoin_betaK d).right]
    induction hx using Algebra.adjoin_induction with
    | mem y hy => rwa [Set.mem_singleton_iff.1 hy]
    | algebraMap r => simp [← frobenius_def]
    | add a b _ _ ha hb => rw [map_add, add_pow_char_pow, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, mul_pow, ha, hb]
  rw [q_iff_frob, frob_iff]
  obtain rfl | hp2 := eq_or_ne p 2
  · -- Both sides hold: `betaK d * (1 - betaK d) = (d + 1) / 4` is even, and `2` is a square mod
    -- `d`.
    have h_prod : π (betaK d) * (1 - π (betaK d)) = 0 := by
      rw [← map_one π, ← map_sub, ← map_mul, betaK_mul_one_sub, map_natCast,
        CharP.cast_eq_zero_iff _ 2]
      grind [PrimeSevenModEight]
    have h_fixed : π (betaK d) ^ 2 = π (betaK d) := by linear_combination -h_prod
    simp [h_fixed, chiK_two]
  · -- Frobenius multiplies `2 * betaK d - 1 = √-d` by the Legendre symbol, so it fixes `betaK d`
    -- iff the symbol is `1` in the residue field or `-d` vanishes there, that is `p = d`.
    have h_sqrt : 2 * π (betaK d) - 1 = π (sqrtNegDInt d) := by simp [map_ofNat]
    have h_fixed : π (betaK d) ^ p ^ 1 = π (betaK d) ↔
        (chiK d p : _ ⧸ w.asIdeal) = 1 ∨ π (sqrtNegDInt d) = 0 := by
      rw [eq_comm, eq_map_betaK_pow_iff hp2 π, h_sqrt, eq_comm, mul_left_eq_self₀, pow_one]
    have h_ramified : π (sqrtNegDInt d) = 0 ↔ p = d := by
      rw [← sq_eq_zero_iff, map_sqrtNegDInt_sq π, neg_eq_zero, CharP.cast_eq_zero_iff _ p,
        Nat.prime_dvd_prime_iff_eq hp.1 Fact.out]
    have h_neg : (-1 : 𝓞 (QuadField d) ⧸ w.asIdeal) ≠ 1 :=
      Ring.neg_one_ne_one_of_char_ne_two (by rwa [ringChar.eq _ p])
    rw [h_fixed, h_ramified]
    obtain ⟨h_eq, h_symbol⟩ | ⟨h_ne, h_symbol | h_symbol⟩ := chiK_cases d p
    · rw [h_symbol]
      simp [h_eq]
    · simp [h_symbol]
    · simp [h_ne, h_symbol, h_neg]

/-- Let `d ≡ 3 mod 4` and let `w` be a place of `K = ℚ(√-d)` over the prime `p`. Write `u.q` for
the absolute norm of a place `u`. Either `p` is inert, that is, `(p) = w` and `w` has norm `p ^ 2`,
or `(p) = w J` for a place `J`, and `w` and `J` both have norm `p` (here `J = w` is allowed: the
ramified case). -/
lemma span_eq_or_exists_span_eq_mul (hw : (p : 𝓞 (QuadField d)) ∈ w.asIdeal) :
    (span {(p : 𝓞 (QuadField d))} = w.asIdeal ∧ w.q = p ^ 2) ∨
      ∃ J : FinPlace (QuadField d),
        span {(p : 𝓞 (QuadField d))} = w.asIdeal * J.asIdeal ∧ w.q = p ∧ J.q = p := by
  -- Write `(p) = w * J` and take norms: `p ^ 2 = N w * N J` with `N w ≠ 1`.
  obtain ⟨J, hJ : span {(p : 𝓞 (QuadField d))} = w.asIdeal * J⟩ := dvd_span_singleton.2 hw
  have norm_mul : absNorm w.asIdeal * absNorm J = p ^ 2 := by
    simpa [hJ, ← Nat.cast_mul, sq] using absNorm_span_eq_mul_star d p
  obtain rfl | hJ_top := eq_or_ne J ⊤
  · -- `p` is inert: `(p) = w` and `N w = p ^ 2`.
    exact .inl ⟨by simpa using hJ, by simpa using norm_mul⟩
  · -- Both norms are `p`, so `J` is prime.
    obtain ⟨norm_w, norm_J⟩ : absNorm w.asIdeal = p ∧ absNorm J = p := by
      simpa [hJ_top, hp.1.mul_eq_prime_sq_iff, w.isPrime.ne_top] using norm_mul
    have norm_irreducible : Irreducible (absNorm J) := by
      simpa [norm_J, Nat.irreducible_iff_prime, Nat.prime_iff] using hp.1
    have J_prime : Prime J := (irreducible_of_irreducible_absNorm norm_irreducible).prime
    exact .inr ⟨ofPrime J_prime, hJ, norm_w, norm_J⟩

/-- Let `d ≡ 3 mod 4` and let `w` be a place of `K = ℚ(√-d)` over the prime `p`. Write `u.q` for
the absolute norm of a place `u`. There is a place `J` such that
(a) the places over `p` are exactly `w` and `J`;
(b) either `J = w` has norm `p ^ 2` (the inert case), or `w` and `J` both have norm `p` and
`(p) = w J` (here `J = w` is allowed: the ramified case). -/
lemma prime_inert_or_eq_mul (hw : (p : 𝓞 (QuadField d)) ∈ w.asIdeal) :
    ∃ J : FinPlace (QuadField d),
      (∀ u : FinPlace (QuadField d), (p : 𝓞 (QuadField d)) ∈ u.asIdeal ↔ u = w ∨ u = J) ∧
      (w = J ∧ w.q = p ^ 2 ∨
        w.q = p ∧ J.q = p ∧ span {(p : 𝓞 (QuadField d))} = w.asIdeal * J.asIdeal) := by
  obtain ⟨h_span, norm_w⟩ | ⟨J, h_span, norm_w, norm_J⟩ := span_eq_or_exists_span_eq_mul w hw
  · refine ⟨w, fun u ↦ ?_, .inl ⟨rfl, norm_w⟩⟩
    rw [w.mem_asIdeal_iff_of_span_eq h_span, or_self]
  · exact ⟨J, w.mem_asIdeal_iff_of_span_eq_mul h_span, .inr ⟨norm_w, norm_J, h_span⟩⟩

end New.QuadField

end QuadFieldSplitting

end
