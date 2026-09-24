import Surreal.Foundations.OmnificPurelyInfiniteIdeal
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Irreducibles and failure of atomic factorization

The factorization proposition `odg:prop:irreduciblect`. Constant
irreducibles are ordinary signed primes. A nonconstant irreducible must
have unit integer constant term, but the displayed quadratic examples
show that this condition does not suffice. A positive monomial witnesses
failure of factorization into irreducibles, even up to a unit, and hence
failure of Mathlib's unique-factorization property.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Integer casting preserves and reflects being an omnific unit. -/
theorem omnific_isUnit_intCast_iff (n : ℤ) :
    IsUnit (omnificIntCast.{u} n) ↔ IsUnit n :=
  ⟨fun h => by simpa only [omnificConstantCoeff_intCast] using h.map omnificConstantCoeff,
    fun h => h.map omnificIntCast⟩

/-- An ordinary integer is irreducible in the omnific ring exactly when it is irreducible in `ℤ`. -/
theorem omnific_irreducible_intCast_iff (n : ℤ) :
    Irreducible (omnificIntCast.{u} n) ↔ Irreducible n := by
  constructor
  · intro h
    refine ⟨fun hu => h.not_isUnit (hu.map omnificIntCast), ?_⟩
    intro a b hab
    have he : omnificIntCast.{u} n = omnificIntCast a * omnificIntCast b := by
      rw [hab, map_mul]
    exact (h.isUnit_or_isUnit he).imp (omnific_isUnit_intCast_iff a).mp
      (omnific_isUnit_intCast_iff b).mp
  · intro h
    refine ⟨fun hu => h.not_isUnit ((omnific_isUnit_intCast_iff n).mp hu), ?_⟩
    intro a b hab
    obtain ⟨r, rfl, _⟩ := (omnific_dvd_int_iff a n h.ne_zero).mp ⟨b, hab⟩
    obtain ⟨s, rfl, _⟩ := (omnific_dvd_int_iff b n h.ne_zero).mp
      ⟨omnificIntCast r, hab.trans (mul_comm _ _)⟩
    have he := congrArg omnificConstantCoeff hab
    simp only [map_mul, omnificConstantCoeff_intCast] at he
    exact (h.isUnit_or_isUnit he).imp (fun hu => hu.map omnificIntCast)
      (fun hu => hu.map omnificIntCast)

/-- Constant irreducibles are exactly signed ordinary primes, expressed by prime absolute value. -/
theorem omnific_irreducible_intCast_iff_prime_natAbs (n : ℤ) :
    Irreducible (omnificIntCast.{u} n) ↔ n.natAbs.Prime := by
  rw [omnific_irreducible_intCast_iff, irreducible_iff_prime, Int.prime_iff_natAbs_prime]

/-- A nonconstant irreducible has integer constant term `1` or `-1`. -/
theorem omnific_nonconstant_irreducible_constant (x : OmnificInteger.{u})
    (hx : Irreducible x) (hn : ¬ ∃ n : ℤ, x = omnificIntCast n) :
    omnificConstantCoeff x = 1 ∨ omnificConstantCoeff x = -1 := by
  have hc := omnific_irreducible_constant_ne_zero x hx
  obtain ⟨q, hq⟩ := (omnific_int_dvd_iff (omnificConstantCoeff x) hc x).mpr dvd_rfl
  rcases hx.isUnit_or_isUnit hq with h | h
  · exact Int.isUnit_iff.mp ((omnific_isUnit_intCast_iff _).mp h)
  · rcases (omnific_isUnit_iff q).mp h with he | he
    · exact False.elim (hn ⟨omnificConstantCoeff x, by simpa only [he, mul_one] using hq⟩)
    · exact False.elim (hn ⟨-omnificConstantCoeff x, by
        simpa only [he, mul_neg_one, map_neg] using hq⟩)

/-- Adding an ordinary integer to a nonzero purely infinite element cannot produce a unit. -/
theorem omnific_purelyInfinite_add_int_not_isUnit (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) (n : ℤ) :
    ¬ IsUnit (x + omnificIntCast n) := by
  intro hu
  have hf := nonnegativeSupport_finite_of_isUnit (x + omnificIntCast n).val
    (hu.map omnificSubring.subtype)
  have he := omnific_eq_intConstant_of_finite (x + omnificIntCast n) hf
  change omnificConstantCoeff x = 0 at hx
  simp only [map_add, hx, omnificConstantCoeff_intCast, _root_.zero_add] at he
  exact hx0 (_root_.add_right_cancel (he.trans (_root_.zero_add _).symm))

/-- Adding any ordinary integer to a nonzero purely infinite element remains nonconstant. -/
theorem omnific_purelyInfinite_add_int_nonconstant (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) (n : ℤ) :
    ¬ ∃ m : ℤ, x + omnificIntCast n = omnificIntCast m := by
  rintro ⟨m, he⟩
  have hc := congrArg omnificConstantCoeff he
  change omnificConstantCoeff x = 0 at hx
  simp only [map_add, hx, omnificConstantCoeff_intCast, _root_.zero_add] at hc
  rw [← hc] at he
  exact hx0 (_root_.add_right_cancel (he.trans (_root_.zero_add _).symm))

/-- A nonconstant factor times a nonzero omnific integer is still nonconstant. -/
theorem omnific_mul_nonconstant (a b : OmnificInteger.{u})
    (ha : ¬ ∃ n : ℤ, a = omnificIntCast n) (hb : b ≠ 0) :
    ¬ ∃ n : ℤ, a * b = omnificIntCast n := by
  rintro ⟨n, hn⟩
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simpa only [map_zero] using h⟩
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hn
    exact mul_ne_zero ha0 hb hn
  obtain ⟨m, hm, _⟩ := (omnific_dvd_int_iff a n hn0).mp ⟨b, hn.symm⟩
  exact ha ⟨m, hm⟩

/-- The source's square example has constant term one but is reducible. -/
theorem omnific_square_add_one_counterexample (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) :
    omnificConstantCoeff ((x + 1) ^ 2) = 1 ∧ ¬ Irreducible ((x + 1) ^ 2) := by
  have hu : ¬ IsUnit (x + 1) := by
    simpa only [map_one] using omnific_purelyInfinite_add_int_not_isUnit x hx hx0 1
  constructor
  · change omnificConstantCoeff x = 0 at hx
    simp only [map_pow, map_add, map_one, hx, _root_.zero_add, one_pow]
  · intro h
    exact (h.isUnit_or_isUnit (pow_two (x + 1))).elim hu hu

/-- The source's difference-of-squares example has constant term minus one but is reducible. -/
theorem omnific_square_sub_one_counterexample (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) :
    omnificConstantCoeff (x ^ 2 - 1) = -1 ∧ ¬ Irreducible (x ^ 2 - 1) := by
  have hplus : ¬ IsUnit (x + 1) := by
    simpa only [map_one] using omnific_purelyInfinite_add_int_not_isUnit x hx hx0 1
  have hminus : ¬ IsUnit (x - 1) := by
    simpa only [map_neg, map_one, sub_eq_add_neg] using
      omnific_purelyInfinite_add_int_not_isUnit x hx hx0 (-1)
  constructor
  · change omnificConstantCoeff x = 0 at hx
    simp only [map_sub, map_pow, map_one, hx, zero_pow (by decide : 2 ≠ 0), zero_sub]
  · intro h
    exact (h.isUnit_or_isUnit (show x ^ 2 - 1 = (x - 1) * (x + 1) by ring)).elim hminus hplus

/-- Both reducible quadratic examples are nonconstant, as required for the failed converse. -/
theorem omnific_square_examples_nonconstant (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) :
    (¬ ∃ n : ℤ, (x + 1) ^ 2 = omnificIntCast n) ∧
      (¬ ∃ n : ℤ, x ^ 2 - 1 = omnificIntCast n) := by
  have hplus : ¬ ∃ n : ℤ, x + 1 = omnificIntCast n := by
    simpa only [map_one] using omnific_purelyInfinite_add_int_nonconstant x hx hx0 1
  have hminus : ¬ ∃ n : ℤ, x - 1 = omnificIntCast n := by
    simpa only [map_neg, map_one, sub_eq_add_neg] using
      omnific_purelyInfinite_add_int_nonconstant x hx hx0 (-1)
  have hp0 : x + 1 ≠ 0 := fun h => hplus ⟨0, by simpa only [map_zero] using h⟩
  constructor
  · rw [pow_two]
    exact omnific_mul_nonconstant _ _ hplus hp0
  · rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact omnific_mul_nonconstant _ _ hminus hp0

/-- A purely infinite element is not associated to any finite product of irreducibles. -/
theorem omnific_purelyInfinite_not_associated_prod (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (s : Multiset OmnificInteger.{u})
    (hs : ∀ p ∈ s, Irreducible p) : ¬ Associated s.prod x := by
  intro he
  have hmem := Ideal.mem_of_dvd omnificPurelyInfiniteIdeal he.symm.dvd hx
  have hnot := omnific_irreducible_prod_not_purelyInfinite s.toList
    (fun p hp => hs p (Multiset.mem_toList.mp hp))
  rw [Multiset.prod_toList] at hnot
  exact hnot hmem

/-- The positive monomial of exponent one witnesses failure of atomic factorization. -/
theorem omnific_not_atomic :
    ¬ (∀ x : OmnificInteger.{u}, x ≠ 0 → ¬ IsUnit x →
      ∃ s : Multiset OmnificInteger, (∀ p ∈ s, Irreducible p) ∧ Associated s.prod x) := by
  intro h
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
  obtain ⟨s, hs, he⟩ := h w (omnificMonomial_ne_zero _ _)
    (omnific_not_isUnit_of_purelyInfinite w hw)
  exact omnific_purelyInfinite_not_associated_prod w hw s hs he

/-- Omnific divisibility is not well founded in Mathlib's factorization sense. -/
theorem omnific_not_wfDvdMonoid : ¬ WfDvdMonoid OmnificInteger.{u} := by
  intro h
  letI := h
  apply omnific_not_atomic
  intro x hx _
  exact WfDvdMonoid.exists_factors x hx

/-- The actual omnific ring is not a unique factorization domain. -/
theorem omnific_not_uniqueFactorizationMonoid : ¬ UniqueFactorizationMonoid OmnificInteger.{u} := by
  intro h
  letI := h
  exact omnific_not_wfDvdMonoid inferInstance

end
end Surreal.Foundations.SignSequence
