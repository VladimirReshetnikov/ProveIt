import Surreal.Foundations.OmnificRealScaling
import Surreal.Foundations.OmnificSupportBounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Bezout

/-!
# Omnific pairs without a greatest common divisor

The full theorem `odg:thm:nogcd`. Irrationally proportional omnific integers
have zero constant terms. A common divisor of a nonzero purely infinite
integer and its irrational real multiple can therefore always be enlarged
by a nonunit monomial. This rules out a greatest common divisor and proves
that the actual omnific ring is neither a GCD domain nor a Bezout domain.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Irrationally proportional omnific integers both have zero constant coefficient. -/
theorem omnific_irrational_proportional_purelyInfinite (r : ℝ) (hr : Irrational r)
    (a b : OmnificInteger.{u})
    (he : omnificToSurreal b = ofReal r * omnificToSurreal a) :
    a ∈ omnificPurelyInfiniteIdeal ∧ b ∈ omnificPurelyInfiniteIdeal := by
  have hev : b.val = realConstants r * a.val := Subtype.ext he
  have hc (x : OmnificInteger.{u}) : (omnificConstantCoeff x : ℝ) = constantCoeff x.val :=
    CoefficientPullback.embedding_retraction constantCoeff (Int.castRingHom ℝ) Int.cast_injective x
  have h := congrArg constantCoeff hev
  rw [map_mul, constantCoeff_realConstants, ← hc, ← hc] at h
  have ha : omnificConstantCoeff a = 0 := by
    by_contra hn
    have hn' : (omnificConstantCoeff a : ℝ) ≠ 0 := by exact_mod_cast hn
    exact hr.ne_rational _ _ ((eq_div_iff hn').mpr h.symm)
  have hb : omnificConstantCoeff b = 0 := by
    rw [ha, Int.cast_zero, mul_zero] at h
    exact_mod_cast h
  exact ⟨ha, hb⟩

/-- Every common divisor of an irrationally proportional nonzero pair has a strictly larger
common divisor in the divisibility order. -/
theorem omnific_common_divisor_strict_enlargement (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (ht0 : t ≠ 0) (r : ℝ) (hr : Irrational r)
    (d : OmnificInteger.{u}) (hdt : d ∣ t) (hdr : d ∣ omnificRealScale r t ht) :
    ∃ e : OmnificInteger.{u}, e ∣ t ∧ e ∣ omnificRealScale r t ht ∧ d ∣ e ∧ ¬ e ∣ d := by
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero ht0 hdt
  obtain ⟨a, ha⟩ := hdt
  obtain ⟨b, hb⟩ := hdr
  have hd' : omnificToSurreal d ≠ 0 :=
    fun h => hd (omnificToSurreal_injective (by simpa using h))
  have he : omnificToSurreal b = ofReal r * omnificToSurreal a := by
    apply mul_left_cancel₀ hd'
    have h := congrArg omnificToSurreal hb
    rw [omnificToSurreal_realScale, ha, map_mul, map_mul] at h
    calc
      _ = ofReal r * (omnificToSurreal d * omnificToSurreal a) := h.symm
      _ = _ := by ring
  obtain ⟨haI, hbI⟩ := omnific_irrational_proportional_purelyInfinite r hr a b he
  obtain ⟨δ, hδ, hq⟩ := omnific_common_monomial_divisor
    (fun c : Bool => if c then a else b) (fun c => by cases c <;> assumption)
  obtain ⟨a', _, ha'⟩ := hq true
  obtain ⟨b', _, hb'⟩ := hq false
  simp at ha' hb'
  let m := omnificMonomial δ hδ
  refine ⟨d * m, ⟨a', ?_⟩, ⟨b', ?_⟩, ⟨m, rfl⟩, ?_⟩
  · rw [ha, ha', mul_assoc]
  · rw [hb, hb', mul_assoc]
  · intro hback
    have hm : m ∣ (1 : OmnificInteger.{u}) :=
      (mul_dvd_mul_iff_left hd).mp (by simpa only [_root_.mul_one] using hback)
    exact omnific_not_isUnit_of_purelyInfinite m
      (omnificMonomial_mem_purelyInfinite δ hδ) (isUnit_iff_dvd_one.mpr hm)

/-- A nonzero purely infinite omnific integer and its irrational real multiple have no gcd. -/
theorem omnific_no_gcd_irrational_multiple (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (ht0 : t ≠ 0) (r : ℝ) (hr : Irrational r) :
    ¬ ∃ d : OmnificInteger.{u}, d ∣ t ∧ d ∣ omnificRealScale r t ht ∧
      ∀ e : OmnificInteger.{u}, e ∣ t → e ∣ omnificRealScale r t ht → e ∣ d := by
  rintro ⟨d, hdt, hdr, hd⟩
  obtain ⟨e, het, her, _, he⟩ := omnific_common_divisor_strict_enlargement t ht ht0 r hr d hdt hdr
  exact he (hd e het her)

/-- The ideal of an irrationally proportional nonzero purely infinite pair is not principal. -/
theorem omnific_irrational_pair_not_principal (t : OmnificInteger.{u})
    (ht : t ∈ omnificPurelyInfiniteIdeal) (ht0 : t ≠ 0) (r : ℝ) (hr : Irrational r) :
    ¬ (Ideal.span {t, omnificRealScale r t ht}).IsPrincipal := by
  intro h
  letI := h
  apply omnific_no_gcd_irrational_multiple t ht ht0 r hr
  exact ⟨_, IsBezout.gcd_dvd_left _ _, IsBezout.gcd_dvd_right _ _,
    fun _ ha hb => IsBezout.dvd_gcd ha hb⟩

/-- The pair omega and sqrt(2) omega has no greatest common divisor. -/
theorem omnific_omega_sqrt_two_no_gcd :
    let t := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
    let ht := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
    ¬ ∃ d : OmnificInteger.{u}, d ∣ t ∧ d ∣ omnificRealScale (Real.sqrt 2) t ht ∧
      ∀ e : OmnificInteger.{u}, e ∣ t → e ∣ omnificRealScale (Real.sqrt 2) t ht → e ∣ d :=
  omnific_no_gcd_irrational_multiple _ _ (omnificMonomial_ne_zero _ _) _ irrational_sqrt_two

/-- The actual omnific ring admits no GCD monoid structure. -/
theorem omnific_not_isGCDMonoid : ¬ IsGCDMonoid OmnificInteger.{u} := by
  rintro ⟨h⟩
  letI := h
  apply omnific_omega_sqrt_two_no_gcd
  exact ⟨_, gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ ha hb => dvd_gcd ha hb⟩

/-- The actual omnific ring is not a Bezout domain. -/
theorem omnific_not_isBezout : ¬ IsBezout OmnificInteger.{u} := by
  intro h
  letI := h
  exact omnific_not_isGCDMonoid inferInstance

end
end Surreal.Foundations.SignSequence
