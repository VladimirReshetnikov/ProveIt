import GRHArticle.ClassGroups.SixthNormCollisionBound
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The small-prime obstruction in quadratic character notation
-/

namespace GRHArticle.ClassGroups

/-- A discriminant supplies a nonzero square witness at a prime precisely
when its Legendre symbol is one. This also handles ramification, where
the discriminant is zero in the residue field. -/
theorem legendreSym_neg_eq_one_iff {x r : ℕ} [Fact r.Prime] :
    legendreSym r (-(x:ℤ)) = 1 ↔ ∃ a : ZMod r, a ≠ 0 ∧ a^2 = -(x:ZMod r) := by
  constructor
  · intro h
    have hnon : Int.cast (-(x:ℤ)) ≠ (0:ZMod r) := by
      intro hzero
      have hz := (legendreSym.eq_zero_iff r (-(x:ℤ))).mpr hzero
      rw [h] at hz
      contradiction
    obtain ⟨a,ha⟩ := (legendreSym.eq_one_iff r hnon).mp h
    refine ⟨a,fun hzero ↦ hnon (by simpa [hzero] using ha),?_⟩
    simpa [pow_two] using ha.symm
  · rintro ⟨a,ha,he⟩
    have hnon : Int.cast (-(x:ℤ)) ≠ (0:ZMod r) := by
      intro hzero
      apply pow_ne_zero 2 ha
      exact he.trans (by simpa using hzero)
    exact (legendreSym.eq_one_iff r hnon).mpr ⟨a, by simpa [pow_two] using he.symm⟩

/-- The arithmetic obstruction is precisely the absence of a positive
quadratic character value at the witness primes. -/
theorem noSixthDiscriminantSquareWitness_iff_legendre (x : ℕ) :
    NoSixthDiscriminantSquareWitness x ↔
      ∀ r, ∀ hr : r.Prime, 19 ≤ r → r ≤ 151 →
        @legendreSym r ⟨hr⟩ (-(x:ℤ)) ≠ 1 := by
  constructor
  · intro h r hr hlo hhi hval
    letI : Fact r.Prime := ⟨hr⟩
    obtain ⟨a,ha,he⟩ := legendreSym_neg_eq_one_iff.mp hval
    exact h r hr hlo hhi a ha he
  · intro h r hr hlo hhi a ha he
    letI : Fact r.Prime := ⟨hr⟩
    exact h r hr hlo hhi (legendreSym_neg_eq_one_iff.mpr ⟨a,ha,he⟩)

end GRHArticle.ClassGroups
