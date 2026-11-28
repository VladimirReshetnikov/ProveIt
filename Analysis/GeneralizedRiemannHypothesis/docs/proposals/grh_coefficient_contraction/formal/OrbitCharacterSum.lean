import Mathlib

/-!
# Character sums on finite transporter fibres

STATUS: UNCOMPILED source draft. No Lean executable was available.

This file supplies the elementary finite-character component of the proposed
first-datum normalization. It does not formalize the source-specific gauge
action, its stabilizer, the compatible modulus reductions, or their CRT
comparison. Those are separate integration obligations described in the report.

The torsor theorem takes an explicit equivalence and factorization of the
weights. In the application the fibre is `g₀ H`, the equivalence is left
multiplication by `g₀`, and the weight factorization is multiplicativity of
the finite-order character.
-/

namespace GRHOrbitAverage

open Finset

/-- A character sum over a finite group is zero or the group cardinality.
The domain group need not be commutative. -/
theorem character_sum_zero_or_card
    {G : Type*} [Group G] [Fintype G] (χ : G →* ℂ) :
    (∑ g : G, χ g) = 0 ∨ (∑ g : G, χ g) = (Fintype.card G : ℂ) := by
  classical
  by_cases h : ∀ g : G, χ g = 1
  · right
    simp [h]
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    have htranslate : (∑ g : G, χ (a * g)) = ∑ g : G, χ g :=
      (Equiv.mulLeft a).sum_comp χ
    have hmul : χ a * (∑ g : G, χ g) = ∑ g : G, χ g := by
      simpa only [map_mul, mul_sum] using htranslate
    have hzero : (χ a - 1) * (∑ g : G, χ g) = 0 := by
      calc
        _ = χ a * (∑ g : G, χ g) - (∑ g : G, χ g) := by ring
        _ = 0 := by rw [hmul, sub_self]
    exact Or.inl ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha))

/-- A weighted sum on a finite torsor is zero or its cardinality times the
weight at one representative. -/
theorem torsor_sum_zero_or_card_mul
    {H T : Type*} [Group H] [Fintype H] [Fintype T]
    (e : H ≃ T) (χ : H →* ℂ) (w : T → ℂ) (ζ : ℂ)
    (hw : ∀ h : H, w (e h) = ζ * χ h) :
    (∑ t : T, w t) = 0 ∨
      (∑ t : T, w t) = (Fintype.card H : ℂ) * ζ := by
  classical
  have hsum : (∑ t : T, w t) = ζ * ∑ h : H, χ h := by
    calc
      _ = ∑ h : H, w (e h) := (e.sum_comp w).symm
      _ = ∑ h : H, ζ * χ h := by simp_rw [hw]
      _ = ζ * ∑ h : H, χ h := by rw [mul_sum]
  rcases character_sum_zero_or_card χ with hzero | hcard
  · left
    rw [hsum, hzero, mul_zero]
  · right
    rw [hsum, hcard, mul_comm]

/-- The normalization is by the stabilizer cardinality, not by the full
averaging group cardinality. -/
theorem normalized_torsor_sum_zero_or
    {H T : Type*} [Group H] [Fintype H] [Fintype T]
    (e : H ≃ T) (χ : H →* ℂ) (w : T → ℂ) (ζ : ℂ)
    (hw : ∀ h : H, w (e h) = ζ * χ h) :
    ((∑ t : T, w t) / (Fintype.card H : ℂ)) = 0 ∨
      ((∑ t : T, w t) / (Fintype.card H : ℂ)) = ζ := by
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := H))
  rcases torsor_sum_zero_or_card_mul e χ w ζ hw with hzero | hmul
  · left
    simp [hzero]
  · right
    apply (div_eq_iff hcard).2
    simpa only [mul_comm] using hmul

/-- A finite-order representative weight gives zero or a root of unity after
normalization. The empty-transporter case is the separate zero sum. -/
theorem normalized_torsor_sum_zero_or_finOrder
    {H T : Type*} [Group H] [Fintype H] [Fintype T]
    (e : H ≃ T) (χ : H →* ℂ) (w : T → ℂ) (ζ : ℂ)
    (hw : ∀ h : H, w (e h) = ζ * χ h) (hζ : IsOfFinOrder ζ) :
    ((∑ t : T, w t) / (Fintype.card H : ℂ)) = 0 ∨
      IsOfFinOrder ((∑ t : T, w t) / (Fintype.card H : ℂ)) := by
  rcases normalized_torsor_sum_zero_or e χ w ζ hw with hzero | heq
  · exact Or.inl hzero
  · right
    rw [heq]
    exact hζ

end GRHOrbitAverage
