import Surreal.Foundations.OmnificQuotientSize
import Surreal.Foundations.OmnificPurelyInfiniteIdeal

/-!
# Principal quotients of the actual omnific ring

The real omnific instance of `osq:prop:principal`. Distinct monomials below
a nonconstant generator's leading exponent have distinct residues. A
principal quotient is small exactly for a nonzero ordinary integer generator.
Among small-quotient ideals, Pi is the only one without small generators.
-/

universe u v
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

/-- Divisibility of nonzero omnific integers cannot decrease the leading growth exponent. -/
theorem omnific_leadingExponent_le_of_dvd (f g : OmnificInteger.{u})
    (hg : omnificToSurreal g ≠ 0) (hfg : f ∣ g) :
    leadingExponent (omnificToSurreal f) ≤ leadingExponent (omnificToSurreal g) := by
  obtain ⟨q, he⟩ := hfg
  have hv := congrArg omnificToSurreal he
  rw [map_mul] at hv
  have hn : omnificToSurreal f * omnificToSurreal q ≠ 0 := hv ▸ hg
  have hd := nonnegativeSupport_leadingExponent_nonneg q.val (mul_ne_zero_iff.mp hn).2
  change 0 ≤ leadingExponent (omnificToSurreal q) at hd
  rw [hv, leadingExponent_mul (mul_ne_zero_iff.mp hn).1 (mul_ne_zero_iff.mp hn).2]
  linarith

/-- The difference of two distinct monomials below a bound still has leading exponent below it. -/
theorem omegaPower_difference_leadingExponent_lt (a b c : SignSequence.{u})
    (hab : a ≠ b) (ha : a < c) (hb : b < c) :
    leadingExponent (omegaPower a - omegaPower b) < c := by
  have hn : omegaPower a - omegaPower b ≠ 0 :=
    sub_ne_zero.mpr (omegaPower_strictMono.injective.ne hab)
  have hs := leadingExponent_mem_normalForm hn
  rw [mem_support, normalForm_sub, normalForm_omegaPower, normalForm_omegaPower, coeff_sub] at hs
  by_cases hea : leadingExponent (omegaPower a - omegaPower b) = a
  · rw [hea]
    exact ha
  by_cases heb : leadingExponent (omegaPower a - omegaPower b) = b
  · rw [heb]
    exact hb
  simp only [coeff_single, if_neg hea, if_neg heb, sub_self, ne_eq, not_true_eq_false] at hs

/-- Distinct positive monomials below the generator's degree cannot be congruent modulo it. -/
theorem omnific_principal_monomial_difference_not_mem (f : OmnificInteger.{u})
    (a b : SignSequence.{u}) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haf : a < leadingExponent (omnificToSurreal f))
    (hbf : b < leadingExponent (omnificToSurreal f)) :
    omnificMonomial a ha - omnificMonomial b hb ∉ Ideal.span ({f} : Set OmnificInteger) := by
  intro hmem
  have hg : omnificToSurreal (omnificMonomial a ha - omnificMonomial b hb) ≠ 0 := by
    rw [map_sub, omnificToSurreal_monomial, omnificToSurreal_monomial]
    exact sub_ne_zero.mpr (omegaPower_strictMono.injective.ne hab)
  have he := omnific_leadingExponent_le_of_dvd f _ hg (Ideal.mem_span_singleton.mp hmem)
  rw [map_sub, omnificToSurreal_monomial, omnificToSurreal_monomial] at he
  exact (omegaPower_difference_leadingExponent_lt a b _ hab haf hbf).not_ge he

/-- Every monomial in the indicated open interval has a different principal-quotient residue. -/
theorem omnific_principal_interval_injective (f : OmnificInteger.{u}) :
    Function.Injective (fun a : Set.Ioo (0 : SignSequence.{u}) (leadingExponent (omnificToSurreal f)) =>
      Ideal.Quotient.mk (Ideal.span {f}) (omnificMonomial a.val a.property.1)) := by
  intro a b he
  change Ideal.Quotient.mk (Ideal.span {f}) (omnificMonomial a.val a.property.1) =
    Ideal.Quotient.mk (Ideal.span {f}) (omnificMonomial b.val b.property.1) at he
  by_contra hn
  apply omnific_principal_monomial_difference_not_mem f a.val b.val a.property.1 b.property.1
    (fun h => hn (Subtype.ext h)) a.property.2 b.property.2
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, he, sub_self]

/-- A positive-degree generator has a principal quotient that is not small. -/
theorem omnific_principal_not_small_of_degree_pos (f : OmnificInteger.{u})
    (hf : 0 < leadingExponent (omnificToSurreal f)) :
    ¬ Small.{u} (OmnificInteger.{u} ⧸ Ideal.span {f}) := by
  intro h
  letI := h
  exact positive_interval_not_small _ hf (small_of_injective (omnific_principal_interval_injective f))

/-- Every nonconstant omnific integer has positive leading exponent. -/
theorem omnific_leadingExponent_pos_of_nonconstant (f : OmnificInteger.{u})
    (hf : ¬ ∃ n : ℤ, f = omnificIntCast n) : 0 < leadingExponent (omnificToSurreal f) := by
  have hn : omnificToSurreal f ≠ 0 := by
    intro hz
    have hf0 : f = 0 := omnificToSurreal_injective (hz.trans (map_zero omnificToSurreal).symm)
    exact hf ⟨0, hf0.trans (map_zero omnificIntCast).symm⟩
  by_contra! he
  exact hf ((omnific_isFinite_iff f).mp ((finite_iff_leadingExponent_nonpos hn).mpr he))

/-- Every small index type has a family of distinct residues modulo a nonconstant generator. -/
theorem omnific_principal_arbitrary_small_family (f : OmnificInteger.{u})
    (hf : ¬ ∃ n : ℤ, f = omnificIntCast n) (ι : Type v) [Small.{u} ι] :
    ∃ g : ι → OmnificInteger.{u},
      Function.Injective (fun i => Ideal.Quotient.mk (Ideal.span {f}) (g i)) := by
  apply omnific_quotient_arbitrary_small_family
  intro h
  exact omnific_principal_not_small_of_degree_pos f
    (omnific_leadingExponent_pos_of_nonconstant f hf)
    ((omnific_small_quotient_iff (Ideal.span {f})).mpr h)

/-- The nonconstant principal quotient is nonzero as a ring. -/
theorem omnific_principal_quotient_nontrivial (f : OmnificInteger.{u})
    (hf : ¬ ∃ n : ℤ, f = omnificIntCast n) :
    Nontrivial (OmnificInteger.{u} ⧸ Ideal.span {f}) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro he
  rcases (omnific_isUnit_iff f).mp (Ideal.span_singleton_eq_top.mp he) with h | h
  · exact hf ⟨1, h.trans (map_one omnificIntCast).symm⟩
  · exact hf ⟨-1, by simpa only [map_neg, map_one] using h⟩

/-- Precisely the nonzero ordinary integer generators have small principal quotients. -/
theorem omnific_principal_quotient_small_iff (f : OmnificInteger.{u}) :
    Small.{u} (OmnificInteger.{u} ⧸ Ideal.span {f}) ↔
      ∃ n : ℤ, n ≠ 0 ∧ f = omnificIntCast n := by
  constructor
  · intro h
    letI := h
    rcases omnific_small_quotient_kernel_cases (Ideal.span {f}) with hPi | ⟨n, hn, he⟩
    · exact False.elim (omnificPurelyInfiniteIdeal_ne_span_small {f} hPi)
    · have hd : f ∣ omnificIntCast (n : ℤ) := by
        apply Ideal.mem_span_singleton.mp
        rw [he]
        exact Ideal.mem_span_singleton_self _
      have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      obtain ⟨z, hz, hzd⟩ := (omnific_dvd_int_iff f n hn0).mp hd
      refine ⟨z, ?_, hz⟩
      intro hz0
      rw [hz0, zero_dvd_iff] at hzd
      exact hn0 hzd
  · rintro ⟨n, hn, rfl⟩
    exact small_of_injective (omnificQuotientIntEquiv n hn).injective

/-- Among small-quotient ideals, every ideal except Pi is generated by one ordinary integer. -/
theorem omnific_small_ideal_fg_iff (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] : I.FG ↔ I ≠ omnificPurelyInfiniteIdeal := by
  constructor
  · intro hfg he
    exact omnificPurelyInfiniteIdeal_not_fg (he ▸ hfg)
  · intro hne
    rcases omnific_small_quotient_kernel_cases I with hI | ⟨n, _, rfl⟩
    · exact False.elim (hne hI)
    · exact Submodule.fg_span_singleton _

/-- Pi is the only small-quotient ideal without a birthday-universe-small generating set. -/
theorem omnific_small_ideal_small_generated_iff (I : Ideal OmnificInteger.{u})
    [Small.{u} (OmnificInteger.{u} ⧸ I)] :
    (∃ S : Set OmnificInteger.{u}, Small.{u} S ∧ Ideal.span S = I) ↔ I ≠ omnificPurelyInfiniteIdeal := by
  constructor
  · rintro ⟨S, hS, he⟩ hI
    letI := hS
    exact omnificPurelyInfiniteIdeal_ne_span_small S (he.trans hI)
  · intro hne
    rcases omnific_small_quotient_kernel_cases I with hI | ⟨n, _, rfl⟩
    · exact False.elim (hne hI)
    · exact ⟨{omnificIntCast (n : ℤ)}, inferInstance, rfl⟩

end
end Surreal.Foundations.SignSequence
