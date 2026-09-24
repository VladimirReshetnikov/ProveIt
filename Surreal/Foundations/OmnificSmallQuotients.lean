import Surreal.Algebra.QuotientReflection
import Surreal.Foundations.OmnificSmallTargets

/-!
# Small quotients and reflection of actual omnific quotients

The real omnific instances of `osq:thm:reflection` and `osq:thm:quotients`,
including the full quotient conclusion of `odg:fact:settarget`. A quotient
is small exactly when its ideal contains the purely infinite ideal. The
ordinary modulus zero denotes that ideal, not the zero principal ideal.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Every actual omnific quotient maps canonically onto its ordinary constant quotient. -/
def omnificQuotientReflection (I : Ideal OmnificInteger.{u}) :
    (OmnificInteger.{u} ⧸ I) →+* ℤ ⧸ I.map omnificConstantCoeff :=
  QuotientReflection.reflection omnificConstantCoeff I

/-- Pulling back the ideal of constants adds exactly the purely infinite ideal. -/
theorem omnific_comap_map_constant (I : Ideal OmnificInteger.{u}) :
    (I.map omnificConstantCoeff).comap omnificConstantCoeff = omnificPurelyInfiniteIdeal ⊔ I :=
  QuotientReflection.comap_map omnificConstantCoeff omnificConstantCoeff_surjective I

/-- The reflection kernel is the image of the purely infinite ideal plus the original ideal. -/
theorem omnificQuotientReflection_ker (I : Ideal OmnificInteger.{u}) :
    RingHom.ker (omnificQuotientReflection I) =
      (omnificPurelyInfiniteIdeal ⊔ I).map (Ideal.Quotient.mk I) :=
  QuotientReflection.reflection_ker omnificConstantCoeff omnificConstantCoeff_surjective I

/-- Small target maps cannot distinguish an arbitrary quotient from its ordinary reflection. -/
def omnificQuotientSmallHomEquiv (I : Ideal OmnificInteger.{u})
    (S : Type v) [Ring S] [Small.{u} S] :
    ((OmnificInteger.{u} ⧸ I) →+* S) ≃ ((ℤ ⧸ I.map omnificConstantCoeff) →+* S) :=
  QuotientReflection.homEquiv omnificConstantCoeff omnificIntCast omnificConstantCoeff_intCast
    (fun φ x => omnific_small_hom_eq_constant φ.toNonUnitalRingHom x) I

/-- An omnific quotient is small precisely when its defining ideal contains all infinite parts. -/
theorem omnific_small_quotient_iff (I : Ideal OmnificInteger.{u}) :
    Small.{u} (OmnificInteger.{u} ⧸ I) ↔ omnificPurelyInfiniteIdeal ≤ I := by
  constructor
  · intro h
    letI := h
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (omnific_small_hom_purelyInfinite (Ideal.Quotient.mk I).toNonUnitalRingHom x hx)
  · intro hI
    exact QuotientReflection.small_quotient_of_ker_le
      omnificConstantCoeff omnificConstantCoeff_surjective I hI

/-- The ordinary ideal giving a small quotient is unique. -/
theorem omnific_small_quotient_ideal_unique (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    ∃! J : Ideal ℤ, I = J.comap omnificConstantCoeff :=
  QuotientReflection.ideal_correspondence omnificConstantCoeff omnificConstantCoeff_surjective I
    ((omnific_small_quotient_iff I).mp inferInstance)

/-- Every small quotient has a unique nonnegative ordinary modulus, with zero representing Pi. -/
theorem omnific_small_quotient_modulus_unique (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    ∃! n : ℕ, I = (Ideal.span ({(n : ℤ)} : Set ℤ)).comap omnificConstantCoeff := by
  obtain ⟨J, hJ, huniq⟩ := omnific_small_quotient_ideal_unique I
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · change I = (Ideal.span ({(Ideal.absNorm J : ℤ)} : Set ℤ)).comap omnificConstantCoeff
    rw [Int.ideal_span_absNorm_eq_self]
    exact hJ
  · intro n hn
    have he := huniq (Ideal.span ({(n : ℤ)} : Set ℤ)) hn
    have hc := congrArg (fun K : Ideal ℤ => Nat.card (ℤ ⧸ K)) he
    simpa only [Int.card_ideal_quot, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hc

/-- The canonical equivalence identifies a small quotient with the corresponding ordinary residue ring. -/
def omnificSmallQuotientEquiv (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    (OmnificInteger.{u} ⧸ I) ≃+* ZMod (Ideal.absNorm (I.map omnificConstantCoeff)) :=
  (QuotientReflection.quotientEquiv omnificConstantCoeff omnificConstantCoeff_surjective I
    ((omnific_small_quotient_iff I).mp inferInstance)).trans
    ((Ideal.quotEquivOfEq (Int.ideal_span_absNorm_eq_self (I.map omnificConstantCoeff)).symm).trans
      (Int.quotientSpanNatEquivZMod _))

/-- The characteristic-zero case is Pi; all other small kernels are positive ordinary moduli. -/
theorem omnific_small_quotient_kernel_cases (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    I = omnificPurelyInfiniteIdeal ∨
      ∃ n : ℕ, 0 < n ∧ I = Ideal.span {omnificIntCast (n : ℤ)} := by
  obtain ⟨n, hn, _⟩ := omnific_small_quotient_modulus_unique I
  by_cases hz : n = 0
  · left
    subst n
    change I = Ideal.comap omnificConstantCoeff ⊥
    simpa only [Int.natCast_zero, Ideal.span_singleton_eq_bot.mpr rfl] using hn
  · right
    refine ⟨n, Nat.pos_of_ne_zero hz, ?_⟩
    rw [hn]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
      omnific_int_dvd_iff _ (by exact_mod_cast hz)]

/-- In particular every small quotient is Z or a finite ordinary residue ring, including Z/1Z. -/
theorem omnific_small_quotient_classification (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    (I = omnificPurelyInfiniteIdeal ∧ Nonempty ((OmnificInteger.{u} ⧸ I) ≃+* ℤ)) ∨
      ∃ n : ℕ, 0 < n ∧ I = Ideal.span {omnificIntCast (n : ℤ)} ∧
        Nonempty ((OmnificInteger.{u} ⧸ I) ≃+* ZMod n) := by
  rcases omnific_small_quotient_kernel_cases I with hI | ⟨n, hn, hI⟩
  · exact Or.inl ⟨hI, ⟨(Ideal.quotEquivOfEq hI).trans omnificQuotientEquiv⟩⟩
  · exact Or.inr ⟨n, hn, hI, ⟨(Ideal.quotEquivOfEq hI).trans
      ((omnificQuotientIntEquiv (n : ℤ) (by exact_mod_cast hn.ne')).trans
        (Int.quotientSpanNatEquivZMod n))⟩⟩

end
end Surreal.Foundations.SignSequence
