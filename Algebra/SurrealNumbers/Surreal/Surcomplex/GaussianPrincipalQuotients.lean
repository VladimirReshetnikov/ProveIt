import Surreal.Surcomplex.GaussianInfiniteGenerators

/-!
# Small Gaussian omnific principal quotients

The remaining Gaussian assertions of `osq:prop:principal`: only nonzero
ordinary Gaussian constants give small principal quotients; Pi_C is the
only small-quotient ideal without small generators.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- A Gaussian omnific unit is exactly an ordinary Gaussian unit. -/
theorem gaussianOmnific_isUnit_iff (f : GaussianOmnificInteger.{u}) :
    IsUnit f ↔ ∃ d : GaussianInt, IsUnit d ∧ f = gaussianOmnificConstants.{u} d := by
  constructor
  · intro h
    refine ⟨gaussianOmnificConstantCoeff.{u} f, h.map gaussianOmnificConstantCoeff.{u}, ?_⟩
    apply Subtype.ext
    rw [gaussianOmnificConstants_val, gaussianOmnificConstantCoeff_toComplex]
    exact nonnegativeSupport_unit_eq_constant f.val (h.map gaussianOmnificSubring.subtype)
  · rintro ⟨d, hd, rfl⟩
    exact hd.map gaussianOmnificConstants.{u}

/-- A nonconstant Gaussian generator defines a nonzero principal quotient. -/
theorem gaussianOmnific_principal_quotient_nontrivial (f : GaussianOmnificInteger.{u})
    (hf : ¬ ∃ d : GaussianInt, f = gaussianOmnificConstants.{u} d) :
    Nontrivial (GaussianOmnificInteger.{u} ⧸ Ideal.span {f}) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro he
  obtain ⟨d, _, hd⟩ := (gaussianOmnific_isUnit_iff f).mp (Ideal.span_singleton_eq_top.mp he)
  exact hf ⟨d, hd⟩

/-- A Gaussian principal quotient is small exactly for nonzero ordinary Gaussian generators. -/
theorem gaussianOmnific_principal_quotient_small_iff (f : GaussianOmnificInteger.{u}) :
    Small.{u} (GaussianOmnificInteger.{u} ⧸ Ideal.span {f}) ↔
      ∃ d : GaussianInt, d ≠ 0 ∧ f = gaussianOmnificConstants.{u} d := by
  constructor
  · intro h
    have hf : ∃ d : GaussianInt, f = gaussianOmnificConstants.{u} d := by
      by_contra hn
      exact gaussianOmnific_principal_not_small f hn h
    obtain ⟨d, rfl⟩ := hf
    refine ⟨d, ?_, rfl⟩
    intro hd
    have hPi := (gaussianOmnific_small_quotient_iff
      (Ideal.span {gaussianOmnificConstants.{u} d})).mp h
    rw [hd, map_zero, Ideal.span_singleton_eq_bot.mpr rfl] at hPi
    exact gaussianOmnificPurelyInfiniteIdeal_ne_bot (le_bot_iff.mp hPi)
  · rintro ⟨d, hd, rfl⟩
    exact small_of_injective (gaussianOmnificQuotientConstantEquiv.{u} d hd).injective

/-- Constant principal ideal membership is an ordinary multiple plus a purely infinite remainder. -/
theorem gaussianOmnific_constant_dvd_iff_purelyInfinite_add (d : GaussianInt) (hd : d ≠ 0)
    (x : GaussianOmnificInteger.{u}) :
    gaussianOmnificConstants.{u} d ∣ x ↔
      ∃ j ∈ gaussianOmnificPurelyInfiniteIdeal.{u}, ∃ m : GaussianInt,
        x = j + gaussianOmnificConstants.{u} (d * m) := by
  rw [gaussianOmnific_constant_dvd_iff d hd]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨x - gaussianOmnificConstants.{u} (gaussianOmnificConstantCoeff.{u} x),
      gaussianOmnific_constant_remainder x, m, ?_⟩
    rw [← hm, sub_add_cancel]
  · rintro ⟨j, hj, m, he⟩
    change gaussianOmnificConstantCoeff.{u} j = 0 at hj
    rw [he, map_add, gaussianOmnificConstantCoeff_constants, hj, zero_add]
    exact dvd_mul_right d m

/-- Pi_C is the only small-quotient Gaussian ideal that is not finitely generated. -/
theorem gaussianOmnific_small_ideal_fg_iff (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    I.FG ↔ I ≠ gaussianOmnificPurelyInfiniteIdeal.{u} := by
  constructor
  · intro h he
    exact gaussianOmnificPurelyInfiniteIdeal_not_fg (he ▸ h)
  · intro hn
    rcases gaussianOmnific_small_quotient_kernel_cases I with hI | ⟨d, _, rfl⟩
    · exact False.elim (hn hI)
    · exact Submodule.fg_span_singleton _

/-- Pi_C is also the only small-quotient Gaussian ideal without a small generating set. -/
theorem gaussianOmnific_small_ideal_small_generated_iff (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    (∃ S : Set GaussianOmnificInteger.{u}, Small.{u} S ∧ Ideal.span S = I) ↔
      I ≠ gaussianOmnificPurelyInfiniteIdeal.{u} := by
  constructor
  · rintro ⟨S, hS, he⟩ hI
    letI := hS
    exact gaussianOmnificPurelyInfiniteIdeal_ne_span_small S (he.trans hI)
  · intro hn
    rcases gaussianOmnific_small_quotient_kernel_cases I with hI | ⟨d, _, rfl⟩
    · exact False.elim (hn hI)
    · exact ⟨{gaussianOmnificConstants.{u} d}, inferInstance, rfl⟩

end
end Surreal.Surcomplex
