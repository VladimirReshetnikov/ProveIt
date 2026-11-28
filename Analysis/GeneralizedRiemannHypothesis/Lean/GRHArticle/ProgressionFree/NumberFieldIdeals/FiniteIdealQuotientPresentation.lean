import GRHArticle.ProgressionFree.NumberFieldIdeals.BoundedIdealQuotient
import GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteRingIdealTables

/-!
# Verified finite arithmetic input for ideal enumeration

A concrete integral basis gives finite ring arithmetic modulo the common
modulus by reducing the integer coordinates and multiplication structure
constants. The interface below requires the reduction map, its surjectivity,
and its kernel. All ideal operations are derived from these primitive facts.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- A presentation of the finite residue ring required at one bound.
The executable ring data consists of its enumeration, decidable equality,
and ring operations. This structure certifies the reduction from the order. -/
structure FiniteIdealQuotient (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] (H : ℕ) where
  reduction : 𝓞 K →+* R
  surjective : Function.Surjective reduction
  kernel_eq : RingHom.ker reduction = boundedIdealModulus K H

namespace FiniteIdealQuotient

variable {R : Type*} [CommRing R] {H : ℕ} (P : FiniteIdealQuotient K R H)

theorem modulus_le_comap (J : Ideal R) : boundedIdealModulus K H ≤ J.comap P.reduction := by
  intro x hx
  have hzero : P.reduction x = 0 := (P.kernel_eq.symm ▸ hx : x ∈ RingHom.ker P.reduction)
  change P.reduction x ∈ J
  rw [hzero]
  exact J.zero_mem

private theorem comap_ne_bot (J : Ideal R) : J.comap P.reduction ≠ ⊥ := by
  intro h
  have hx : ((H.factorial^2 : ℕ) : 𝓞 K) ∈ J.comap P.reduction :=
    P.modulus_le_comap J (Ideal.subset_span rfl)
  rw [h, Ideal.mem_bot] at hx
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.factorial_ne_zero _))) hx

/-- Lift a quotient ideal to a nonzero integral ideal in the number field. -/
def lift (J : Ideal R) : (Ideal (𝓞 K))⁰ :=
  ⟨J.comap P.reduction,mem_nonZeroDivisors_iff_ne_zero.mpr (P.comap_ne_bot J)⟩

theorem lift_map_of_modulus_le {I : (Ideal (𝓞 K))⁰} (hI : boundedIdealModulus K H ≤ I.val) :
    P.lift (I.val.map P.reduction) = I := by
  apply Subtype.ext
  change (I.val.map P.reduction).comap P.reduction = I.val
  rw [Ideal.comap_map_of_surjective P.reduction P.surjective, ← RingHom.ker_eq_comap_bot, P.kernel_eq,
    sup_eq_left.mpr hI]

theorem map_lift (J : Ideal R) : (P.lift J).val.map P.reduction = J :=
  Ideal.map_comap_of_surjective P.reduction P.surjective J

theorem lift_injective : Function.Injective P.lift := by
  intro J L h
  simpa only [P.map_lift] using congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ I.val.map P.reduction) h

theorem absNorm_lift (J : Ideal R) : absNorm (P.lift J).val = Nat.card (R ⧸ J) := by
  let f := (Ideal.Quotient.mk J).comp P.reduction
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp P.surjective
  have hk : RingHom.ker f = (P.lift J).val := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hk]
  exact Nat.card_congr (f.quotientKerEquivOfSurjective hf).toEquiv

theorem map_eq_iff {I J : Ideal (𝓞 K)} (hI : boundedIdealModulus K H ≤ I)
    (hJ : boundedIdealModulus K H ≤ J) : I.map P.reduction = J.map P.reduction ↔ I = J := by
  constructor
  · intro he
    have h := congrArg (Ideal.comap P.reduction) he
    rwa [Ideal.comap_map_of_surjective P.reduction P.surjective,
      Ideal.comap_map_of_surjective P.reduction P.surjective, ← RingHom.ker_eq_comap_bot,
      P.kernel_eq, sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at h
  · rintro rfl
    rfl

theorem lift_le_iff {J L : Ideal R} : (P.lift J).val ≤ (P.lift L).val ↔ J ≤ L := by
  constructor
  · intro h
    simpa only [P.map_lift] using Ideal.map_mono (f := P.reduction) h
  · exact Ideal.comap_mono

/-- Lift a prime ideal of the quotient to a genuine prime ideal of the order. -/
def liftPrime (J : Ideal R) (hJ : J.IsPrime) : HeightOneSpectrum (𝓞 K) where
  asIdeal := (P.lift J).val
  isPrime := hJ.comap P.reduction
  ne_bot := P.comap_ne_bot J

/-- A prime ideal within range stays prime after reduction. -/
theorem map_isPrime (p : HeightOneSpectrum (𝓞 K)) (hp : absNorm p.asIdeal ≤ H) :
    (p.asIdeal.map P.reduction).IsPrime := by
  letI := p.isPrime
  apply Ideal.map_isPrime_of_surjective P.surjective
  rw [P.kernel_eq]
  exact boundedIdealModulus_le H (I := primeIdeal p) hp

end FiniteIdealQuotient

/-- An ideal is smooth exactly when it has no prime divisor outside `S`. -/
theorem smooth_iff_no_exterior_prime_dvd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) : I ∈ Set.range (smoothMultiplier S) ↔
      ∀ p ∉ S, ¬ primeIdeal p ∣ I := by
  have hexp {J : (Ideal (𝓞 K))⁰} (p : HeightOneSpectrum (𝓞 K)) :
      primeExponent p J = 0 ↔ ¬ primeIdeal p ∣ J := by
    rw [primeExponent_eq_iff, nonZeroDivisors_dvd_iff_dvd_coe]
    simp [primeIdeal]
  constructor
  · intro hI p hp
    exact (hexp p).mp (primeExponent_smooth_outside S hI hp)
  · intro hI
    have hunit : ∀ p : HeightOneSpectrum (𝓞 K), primeExponent p (1 : (Ideal (𝓞 K))⁰) = 0 := by
      intro p
      apply (hexp p).mpr
      intro h
      rw [nonZeroDivisors_dvd_iff_dvd_coe] at h
      exact (Ideal.prime_of_isPrime p.ne_bot p.isPrime).not_unit (isUnit_of_dvd_one h)
    have hr : idealRoughPart S I = 1 := by
      apply primeExponent_ext
      intro p
      rw [hunit p]
      by_cases hp : p ∈ S
      · exact primeExponent_rough_inside S (idealRoughPart_mem S I) hp
      · have h := congrArg (primeExponent p) (idealRoughPart_mul_smoothPart S I)
        rw [primeExponent_mul, primeExponent_smooth_outside S (idealSmoothPart_mem S I) hp, add_zero] at h
        exact h.trans ((hexp p).mpr (hI p hp))
    have he := idealRoughPart_mul_smoothPart S I
    rw [hr, one_mul] at he
    exact he ▸ idealSmoothPart_mem S I

end GRHArticle.ProgressionFree.NumberFieldIdeals
