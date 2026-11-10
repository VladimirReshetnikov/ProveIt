import DiophantineConsistency.ZRows.CoprimeSquares
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Reduced fractions and the rational root theorem in models of `𝗜𝚺₁`

In the ring of differences `DiffRing V` of a model `V` of `𝗜𝚺₁`:

* `reduced_fraction`: every pair `Z, M` with `M ≠ 0` is `g·z', g·m'` with `g ≠ 0` and
  `IsCoprime z' m'` (Mathlib's ring-theoretic coprimality, a Bezout identity). The gcd comes
  from `ArithmeticGcdNormalization.gcd_certificate_exists`; no induction is used here;
* `dvd_of_pow5`: the rational root theorem for a monic quintic whose lower coefficients carry
  the matching powers of the denominator: if
  `M⁵ ∣ Z⁵ + c₃M²Z³ + c₂M³Z² + c₀M⁵`, then `M ∣ Z`. This is how the saturated carriers of
  the eleven-integer rows recover a divisibility that the stronger circuits enforce by an
  explicit substitution;
* `dvd_of_dvd_mul_coprime`: `M ∣ H·Y` and `IsCoprime H M` give `M ∣ Y` (a named form of
  `IsCoprime.dvd_of_dvd_mul_left`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsReducedFraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ZRowsCoprimeSquares

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Reduced fraction**: `Z = g·z'`, `M = g·m'` with `g ≠ 0` and `z'`, `m'` coprime. -/
theorem reduced_fraction (Z M : DiffRing V) (hM : M ≠ 0) :
    ∃ g z' m' : DiffRing V, Z = g * z' ∧ M = g * m' ∧ g ≠ 0 ∧ IsCoprime z' m' := by
  obtain ⟨a, ha⟩ := abs_eq_ι Z
  obtain ⟨b, hb⟩ := abs_eq_ι M
  have hb0 : (ι b : DiffRing V) ≠ 0 := by rw [← hb]; exact abs_ne_zero.mpr hM
  obtain ⟨g, ⟨a', rfl⟩, ⟨b', rfl⟩, hbez⟩ := gcd_certificate_exists a b
  have hgR : (ι g : DiffRing V) ≠ 0 := by
    intro h0; apply hb0; rw [map_mul, h0, zero_mul]
  have hcop : IsCoprime (ι a' : DiffRing V) (ι b') := by
    obtain ⟨u, v, w, z, he⟩ := hbez
    have he' := congrArg (ι (V := V)) he
    simp only [map_add, map_mul] at he'
    refine ⟨ι w - ι u, ι z - ι v, mul_left_cancel₀ hgR ?_⟩
    linear_combination (-1 : DiffRing V) * he'
  rw [map_mul] at ha hb
  have hZ : ∃ z' : DiffRing V, Z = ι g * z' ∧ IsCoprime z' (ι b' : DiffRing V) := by
    rcases abs_choice Z with h | h
    · exact ⟨ι a', by rw [← ha, h], hcop⟩
    · exact ⟨-ι a', by rw [mul_neg, ← ha, h, neg_neg], hcop.neg_left⟩
  obtain ⟨z', hz', hc⟩ := hZ
  rcases abs_choice M with h | h
  · exact ⟨ι g, z', ι b', hz', by rw [← hb, h], hgR, hc⟩
  · exact ⟨ι g, z', -ι b', hz', by rw [mul_neg, ← hb, h, neg_neg], hgR, hc.neg_right⟩

/-- **Rational root theorem**, in the shape of the saturated carrier: a root of the monic
quintic modulo `M⁵`, with lower coefficients divisible by the matching powers of `M`, is
divisible by `M`. -/
theorem dvd_of_pow5 {Z M c3 c2 c0 : DiffRing V} (hM : M ≠ 0)
    (h : M ^ 5 ∣ Z ^ 5 + c3 * M ^ 2 * Z ^ 3 + c2 * M ^ 3 * Z ^ 2 + c0 * M ^ 5) : M ∣ Z := by
  obtain ⟨g, z', m', hZ, hMg, hg, hc⟩ := reduced_fraction Z M hM
  obtain ⟨t, ht⟩ := h
  rw [hZ, hMg] at ht
  have h1 : z' ^ 5 * 1
      = m' * (m' ^ 4 * t - c3 * m' * z' ^ 3 - c2 * m' ^ 2 * z' ^ 2 - c0 * m' ^ 4) := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hg)
    linear_combination ht
  have hd : m' ∣ 1 := (hc.pow_left (m := 5)).symm.dvd_of_dvd_mul_left ⟨_, h1⟩
  obtain ⟨e, he⟩ := hd
  rw [hZ, hMg]
  exact ⟨z' * e, by linear_combination (g * z') * he⟩

/-- `M ∣ H·Y` and `H`, `M` coprime give `M ∣ Y`. -/
theorem dvd_of_dvd_mul_coprime {H M Y : DiffRing V} (hc : IsCoprime H M) (h : M ∣ H * Y) :
    M ∣ Y :=
  hc.symm.dvd_of_dvd_mul_left h

#print axioms reduced_fraction
#print axioms dvd_of_pow5
#print axioms dvd_of_dvd_mul_coprime

end DiophantineConsistency.ZRowsReducedFraction
