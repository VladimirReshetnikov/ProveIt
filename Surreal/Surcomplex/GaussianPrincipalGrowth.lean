import Surreal.Foundations.OmnificPrincipalQuotients
import Surreal.Surcomplex.GaussianSmallQuotients
import Surreal.Surcomplex.SupportRingHahnEmbedding

/-!
# Degree separation in Gaussian omnific principal quotients

The Gaussian monomial-separation assertion of `osq:prop:principal`.
Divisibility cannot decrease leading exponent. Every nonconstant principal
quotient therefore contains distinct monomial residues in each small cardinality.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Passing from the real axis to the complex plane does not change leading growth. -/
theorem leadingExponent_real (x : SignSequence.{u}) :
    leadingExponent (ofReal x) = SignSequence.leadingExponent x := by
  rw [leadingExponent, modulus_ofReal]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, SignSequence.leadingExponent_neg]

/-- A nonzero Gaussian omnific multiple has at least the degree of its divisor. -/
theorem gaussianOmnific_leadingExponent_le_of_dvd (f g : GaussianOmnificInteger.{u})
    (hg : gaussianOmnificToSurcomplex g ≠ 0) (hfg : f ∣ g) :
    leadingExponent (gaussianOmnificToSurcomplex f) ≤
      leadingExponent (gaussianOmnificToSurcomplex g) := by
  obtain ⟨q, he⟩ := hfg
  have hv := congrArg gaussianOmnificToSurcomplex he
  rw [map_mul] at hv
  have hn : gaussianOmnificToSurcomplex f * gaussianOmnificToSurcomplex q ≠ 0 := hv ▸ hg
  have hd := nonnegativeSupport_leadingExponent_nonneg q.val (mul_ne_zero_iff.mp hn).2
  change 0 ≤ leadingExponent (gaussianOmnificToSurcomplex q) at hd
  rw [hv, leadingExponent_mul (mul_ne_zero_iff.mp hn).1 (mul_ne_zero_iff.mp hn).2]
  linarith

/-- Gaussian coefficients cannot reverse divisibility order between positive real monomials. -/
theorem gaussianOmnificMonomial_le_of_dvd {a b : SignSequence.{u}} (ha : 0 < a) (hb : 0 < b)
    (h : omnificToGaussian (SignSequence.omnificMonomial a ha) ∣
      omnificToGaussian (SignSequence.omnificMonomial b hb)) : a ≤ b := by
  have hn : gaussianOmnificToSurcomplex
      (omnificToGaussian (SignSequence.omnificMonomial b hb)) ≠ 0 := by
    rw [gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial]
    exact (map_ne_zero_iff ofReal ofReal_injective).mpr (SignSequence.omegaPower_ne_zero b)
  have he := gaussianOmnific_leadingExponent_le_of_dvd _ _ hn h
  simpa only [gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial,
    leadingExponent_real, SignSequence.leadingExponent_omegaPower] using he

/-- A Gaussian omnific element that is not an ordinary constant has positive degree. -/
theorem gaussianOmnific_leadingExponent_pos_of_nonconstant (f : GaussianOmnificInteger.{u})
    (hf : ¬ ∃ d : GaussianInt, f = gaussianOmnificConstants.{u} d) :
    0 < leadingExponent (gaussianOmnificToSurcomplex f) := by
  apply nonnegativeSupport_leadingExponent_pos f.val
  intro he
  apply hf
  refine ⟨gaussianOmnificConstantCoeff.{u} f, Subtype.ext ?_⟩
  rw [gaussianOmnificConstants_val, gaussianOmnificConstantCoeff_toComplex]
  exact he

/-- Positive monomials below a generator's degree have distinct principal-ideal residues. -/
theorem gaussianOmnific_principal_monomial_difference_not_mem (f : GaussianOmnificInteger.{u})
    (a b : SignSequence.{u}) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haf : a < leadingExponent (gaussianOmnificToSurcomplex f))
    (hbf : b < leadingExponent (gaussianOmnificToSurcomplex f)) :
    omnificToGaussian (SignSequence.omnificMonomial a ha) -
      omnificToGaussian (SignSequence.omnificMonomial b hb) ∉ Ideal.span {f} := by
  intro hm
  have hn : gaussianOmnificToSurcomplex
      (omnificToGaussian (SignSequence.omnificMonomial a ha) -
        omnificToGaussian (SignSequence.omnificMonomial b hb)) ≠ 0 := by
    rw [map_sub, gaussianOmnificToSurcomplex_of_omnific, gaussianOmnificToSurcomplex_of_omnific,
      SignSequence.omnificToSurreal_monomial, SignSequence.omnificToSurreal_monomial, ← map_sub]
    exact (map_ne_zero_iff ofReal ofReal_injective).mpr
      (sub_ne_zero.mpr (SignSequence.omegaPower_strictMono.injective.ne hab))
  have he := gaussianOmnific_leadingExponent_le_of_dvd f _ hn (Ideal.mem_span_singleton.mp hm)
  rw [map_sub, gaussianOmnificToSurcomplex_of_omnific, gaussianOmnificToSurcomplex_of_omnific,
    SignSequence.omnificToSurreal_monomial, SignSequence.omnificToSurreal_monomial,
    ← map_sub, leadingExponent_real] at he
  exact (SignSequence.omegaPower_difference_leadingExponent_lt a b _ hab haf hbf).not_ge he

/-- The entire open interval of positive exponents below the generator injects into the quotient. -/
theorem gaussianOmnific_principal_interval_injective (f : GaussianOmnificInteger.{u}) :
    Function.Injective (fun a : Set.Ioo (0 : SignSequence.{u})
      (leadingExponent (gaussianOmnificToSurcomplex f)) =>
      Ideal.Quotient.mk (Ideal.span {f})
        (omnificToGaussian (SignSequence.omnificMonomial a.val a.property.1))) := by
  intro a b he
  change Ideal.Quotient.mk (Ideal.span {f})
    (omnificToGaussian (SignSequence.omnificMonomial a.val a.property.1)) =
    Ideal.Quotient.mk (Ideal.span {f})
      (omnificToGaussian (SignSequence.omnificMonomial b.val b.property.1)) at he
  by_contra hn
  apply gaussianOmnific_principal_monomial_difference_not_mem f a.val b.val
    a.property.1 b.property.1 (fun h => hn (Subtype.ext h)) a.property.2 b.property.2
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, he, sub_self]

/-- Every nonconstant Gaussian principal quotient is not small in the birthday universe. -/
theorem gaussianOmnific_principal_not_small (f : GaussianOmnificInteger.{u})
    (hf : ¬ ∃ d : GaussianInt, f = gaussianOmnificConstants.{u} d) :
    ¬ Small.{u} (GaussianOmnificInteger.{u} ⧸ Ideal.span {f}) := by
  intro h
  letI := h
  exact SignSequence.positive_interval_not_small _
    (gaussianOmnific_leadingExponent_pos_of_nonconstant f hf)
    (small_of_injective (gaussianOmnific_principal_interval_injective f))

/-- Every small index type admits actual representatives with distinct principal-quotient residues. -/
theorem gaussianOmnific_principal_arbitrary_small_family (f : GaussianOmnificInteger.{u})
    (hf : ¬ ∃ d : GaussianInt, f = gaussianOmnificConstants.{u} d) (ι : Type v) [Small.{u} ι] :
    ∃ g : ι → GaussianOmnificInteger.{u},
      Function.Injective (fun i => Ideal.Quotient.mk (Ideal.span {f}) (g i)) := by
  let c := leadingExponent (gaussianOmnificToSurcomplex f)
  have hc : 0 < c := gaussianOmnific_leadingExponent_pos_of_nonconstant f hf
  let o : ι → Ordinal.{u} := fun i =>
    Ordinal.typein (@WellOrderingRel (Shrink.{u} ι)) (equivShrink ι i)
  have ho : Function.Injective o :=
    (Ordinal.typein_injective _).comp (equivShrink ι).injective
  let a : ι → Set.Ioo (0 : SignSequence.{u}) c := fun i =>
    ⟨SignSequence.ordinalScale c (o i), SignSequence.ordinalScale_pos c hc (o i),
      by simpa only [Nat.cast_one, one_mul] using
        SignSequence.nat_mul_ordinalScale_lt c hc (o i) 1⟩
  refine ⟨fun i => omnificToGaussian (SignSequence.omnificMonomial (a i).val (a i).property.1), ?_⟩
  intro i j he
  have ha := gaussianOmnific_principal_interval_injective f he
  exact ho ((SignSequence.ordinalScale_injective c hc) (congrArg Subtype.val ha))

end
end Surreal.Surcomplex
