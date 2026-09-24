import Surreal.Foundations.OmnificSmallQuotients
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.RingTheory.Localization.Rat

/-!
# Small prime and field quotients of the actual omnific ring

The real ideal and field-map assertions of `osq:cor:smallprimes`.
The characteristic-zero kernel is the purely infinite ideal, which is
prime but not maximal. All small field quotients have ordinary prime modulus.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The purely infinite ideal is prime because its quotient is the ordinary integer domain. -/
theorem omnificPurelyInfiniteIdeal_isPrime : omnificPurelyInfiniteIdeal.{u}.IsPrime := by
  exact Ideal.comap_isPrime omnificConstantCoeff ⊥

/-- The purely infinite ideal is not maximal: its ordinary integer quotient is not a field. -/
theorem omnificPurelyInfiniteIdeal_not_isMaximal : ¬ omnificPurelyInfiniteIdeal.{u}.IsMaximal := by
  intro h
  have hf := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp h
  exact Int.not_isField (omnificQuotientEquiv.symm.toMulEquiv.isField hf)

/-- Prime ideals with small quotient are precisely Pi and the ordinary prime principal ideals. -/
theorem omnific_small_ideal_isPrime_iff (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    I.IsPrime ↔ I = omnificPurelyInfiniteIdeal ∨
      ∃ p : ℕ, p.Prime ∧ I = Ideal.span {omnificIntCast (p : ℤ)} := by
  constructor
  · intro hp
    rcases omnific_small_quotient_kernel_cases I with h | ⟨n, hn, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, (omnific_nat_span_isPrime_iff n hn.ne').mp (h ▸ hp), h⟩
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · exact omnificPurelyInfiniteIdeal_isPrime
    · exact (omnific_nat_span_isPrime_iff p hp.ne_zero).mpr hp

/-- The maximal ideals among those with small quotient have exactly ordinary prime moduli. -/
theorem omnific_small_ideal_isMaximal_iff (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    I.IsMaximal ↔ ∃ p : ℕ, p.Prime ∧ I = Ideal.span {omnificIntCast (p : ℤ)} := by
  constructor
  · intro h
    rcases (omnific_small_ideal_isPrime_iff I).mp h.isPrime with hI | hI
    · exact False.elim (omnificPurelyInfiniteIdeal_not_isMaximal (hI ▸ h))
    · exact hI
  · rintro ⟨p, hp, rfl⟩
    letI : Fact p.Prime := ⟨hp⟩
    exact omnific_prime_span_isMaximal p

/-- Every small field quotient is an ordinary prime field, including its defining kernel. -/
theorem omnific_small_quotient_isField_iff (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    IsField (OmnificInteger.{u} ⧸ I) ↔
      ∃ p : ℕ, p.Prime ∧ I = Ideal.span {omnificIntCast (p : ℤ)} := by
  rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, omnific_small_ideal_isMaximal_iff]

/-- The native quotient field is explicitly ring-equivalent to the indicated prime field. -/
theorem omnific_small_field_quotient (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] (h : IsField (OmnificInteger.{u} ⧸ I)) :
    ∃ p : ℕ, p.Prime ∧ I = Ideal.span {omnificIntCast (p : ℤ)} ∧
      Nonempty ((OmnificInteger.{u} ⧸ I) ≃+* ZMod p) := by
  obtain ⟨p, hp, hI⟩ := (omnific_small_quotient_isField_iff I).mp h
  exact ⟨p, hp, hI, ⟨(Ideal.quotEquivOfEq hI).trans
    ((omnificQuotientIntEquiv (p : ℤ) (by exact_mod_cast hp.ne_zero)).trans
      (Int.quotientSpanNatEquivZMod p))⟩⟩

/-- The fraction field of the characteristic-zero quotient is the ordinary rational field. -/
def omnificPurelyInfiniteFractionEquiv :
    FractionRing (OmnificInteger.{u} ⧸ omnificPurelyInfiniteIdeal) ≃+* ℚ :=
  IsFractionRing.ringEquivOfRingEquiv omnificQuotientEquiv

/-- The fraction field of an ordinary prime quotient is that same finite prime field. -/
def omnificPrimeFractionEquiv (p : ℕ) [hp : Fact p.Prime] :
    FractionRing (OmnificInteger.{u} ⧸ Ideal.span {omnificIntCast (p : ℤ)}) ≃+* ZMod p :=
  IsFractionRing.ringEquivOfRingEquiv
    ((omnificQuotientIntEquiv (p : ℤ) (by exact_mod_cast hp.out.ne_zero)).trans
      (Int.quotientSpanNatEquivZMod p))

/-- Characteristic-zero small targets have exactly the purely infinite kernel. -/
theorem omnific_small_charZero_ker {K : Type v} [Ring K] [CharZero K] [Small.{u} K]
    (φ : OmnificInteger.{u} →+* K) : RingHom.ker φ = omnificPurelyInfiniteIdeal := by
  ext x
  change φ x = 0 ↔ omnificConstantCoeff x = 0
  rw [omnific_small_ringHom_eq_constant φ x, Int.cast_eq_zero]

/-- In nonzero characteristic p, the small-target kernel is precisely p times the omnific ring. -/
theorem omnific_small_charP_ker {K : Type v} [Ring K] [Small.{u} K]
    (p : ℕ) (hp : p ≠ 0) [CharP K p] (φ : OmnificInteger.{u} →+* K) :
    RingHom.ker φ = Ideal.span {omnificIntCast (p : ℤ)} := by
  ext x
  rw [RingHom.mem_ker, omnific_small_ringHom_eq_constant φ x,
    CharP.intCast_eq_zero_iff K p, Ideal.mem_span_singleton,
    omnific_int_dvd_iff _ (by exact_mod_cast hp)]

/-- In nonzero characteristic the image is explicitly the ordinary residue ring. -/
def omnificSmallCharPRangeEquiv {K : Type v} [Ring K] [Small.{u} K]
    (p : ℕ) (hp : p ≠ 0) [CharP K p] (φ : OmnificInteger.{u} →+* K) :
    φ.range ≃+* ZMod p :=
  (RingHom.quotientKerEquivRange φ).symm.trans
    ((Ideal.quotEquivOfEq (omnific_small_charP_ker p hp φ)).trans
      ((omnificQuotientIntEquiv (p : ℤ) (by exact_mod_cast hp)).trans
        (Int.quotientSpanNatEquivZMod p)))

/-- Every small-target image is exactly the ordinary integer prime subring. -/
theorem omnific_small_ringHom_range {K : Type v} [Ring K] [Small.{u} K]
    (φ : OmnificInteger.{u} →+* K) : φ.range = (Int.castRingHom K).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨omnificConstantCoeff x, (omnific_small_ringHom_eq_constant φ x).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨omnificIntCast n, omnific_hom_intCast φ n⟩

/-- A small characteristic-zero image is explicitly the ordinary integer ring. -/
def omnificSmallCharZeroRangeEquiv {K : Type v}
    [Ring K] [CharZero K] [Small.{u} K] (φ : OmnificInteger.{u} →+* K) : φ.range ≃+* ℤ :=
  (RingHom.quotientKerEquivRange φ).symm.trans
    ((Ideal.quotEquivOfEq (omnific_small_charZero_ker φ)).trans omnificQuotientEquiv)

/-- In characteristic zero the image is an integer ring, not a field. -/
theorem omnific_small_charZero_range_not_isField {K : Type v}
    [Ring K] [CharZero K] [Small.{u} K] (φ : OmnificInteger.{u} →+* K) :
    ¬ IsField φ.range := by
  intro h
  exact Int.not_isField ((omnificSmallCharZeroRangeEquiv φ).symm.toMulEquiv.isField h)

end
end Surreal.Foundations.SignSequence
