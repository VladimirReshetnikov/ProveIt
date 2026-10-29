import DiophantineConsistency.ThirteenCarrierSoundness
import DiophantineConsistency.CurrentPositiveZero2011

/-!
# Correcting the strong factor of the thirteen-coordinate unit product

The ports and thirteen coordinates are exactly those of `ThirteenCarrier`.
Adding `P-1` inside the strong coefficient changes the polynomial, but preserves
its entire strictly positive integer zero set. Crucially, `P = 1` is derived
separately from either zero: positivity excludes the negative Pell unit before
any equation is assumed. The current fixed-port consistency specialization is
external Lean mathematics, not an encoded ZFC proof.
-/

namespace DiophantineConsistency.ThirteenCorrectedStrong

set_option Elab.async false
set_option maxRecDepth 10000

open ThirteenCarrierSoundness

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The old strong coefficient plus the first norm residual. -/
def correctedStrong (b : Carrier65.Core R) : R :=
  b.f ^ 2 - (b.i ^ 2 * b.c ^ 2) * (b.delta * b.c ^ 2 + (b.P - 1))

theorem correctedStrong_eq (b : Carrier65.Core R) :
    correctedStrong b = Carrier65.strong b - (b.i * b.c) ^ 2 * (b.P - 1) := by
  unfold correctedStrong Carrier65.strong
  ring

/-- Exact cancellation used in the separate complete degree audit. Here
`E=X*Y`, `a=E+Y`, `c=k*Y+eta`, and tau remains an arbitrary polynomial. -/
theorem coefficient_cancellation (X Y k eta H tau : R) :
    ((X * Y + Y) ^ 2 + H) * (k * Y + eta) ^ 2 +
      (tau ^ 2 - (X * Y * k * Y) * (X * Y * k * Y + k) - 1) =
    ((2 * X + 1) * Y ^ 2 + H) * (k * Y + eta) ^ 2 +
      (X * Y) ^ 2 * eta * (2 * k * Y + eta) - X * Y * k ^ 2 * Y + tau ^ 2 - 1 := by
  ring

theorem strong_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    Carrier65.strong (data p v) =
      (ThirteenCarrier.core p v).f ^ 2 -
        (ThirteenCarrier.core p v).delta * (ThirteenCarrier.core p v).t ^ 2 := by
  change (data p v).f ^ 2 - (data p v).delta *
    ((b p v * v 4) * (data p v).c ^ 2) ^ 2 =
    (data p v).f ^ 2 - (data p v).delta *
      (b p v * v 4 * (data p v).c ^ 2) ^ 2
  rfl

def value (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let c := ThirteenCarrier.core p v
  c.P * c.Q * (c.delta * (c.f ^ 2 - 1) * c.gap + c.y ^ 2) *
    correctedStrong (data p v) - 1

/-- Exact polynomial difference; the two polynomials are not identical. -/
theorem correction_identity (p : Fin 4 → R) (v : Fin 13 → R) :
    value p v = ThirteenCarrier.value71 p v -
      (ThirteenCarrier.core p v).P * (ThirteenCarrier.core p v).Q *
        ((ThirteenCarrier.core p v).delta * ((ThirteenCarrier.core p v).f ^ 2 - 1) *
          (ThirteenCarrier.core p v).gap + (ThirteenCarrier.core p v).y ^ 2) *
        ((data p v).i * (data p v).c) ^ 2 * ((ThirteenCarrier.core p v).P - 1) := by
  unfold value
  rw [correctedStrong_eq, strong_shape]
  unfold ThirteenCarrier.value71
  change (ThirteenCarrier.core p v).P * (ThirteenCarrier.core p v).Q *
    ((ThirteenCarrier.core p v).delta * ((ThirteenCarrier.core p v).f ^ 2 - 1) *
      (ThirteenCarrier.core p v).gap + (ThirteenCarrier.core p v).y ^ 2) *
    ((ThirteenCarrier.core p v).f ^ 2 - (ThirteenCarrier.core p v).delta *
      (ThirteenCarrier.core p v).t ^ 2 -
      ((data p v).i * (data p v).c) ^ 2 * ((ThirteenCarrier.core p v).P - 1)) - 1 = _
  ring

/-- This exclusion holds on every positive assignment, without a zero premise. -/
theorem first_ne_neg_one (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : (ThirteenCarrier.core p v).P ≠ -1 := by
  have hp := parent_pos p v hb hv (z := 1) (y := 1) (by norm_num) (by norm_num)
  change (Carrier65.core p (parent p v 1 1)).P ≠ -1
  rw [Carrier65.first_shape]
  exact ConsecutivePell.norm_ne_neg_one _ _ _
    (Carrier65.firstParameter_ge_two p (parent p v 1 1) hb hp)

theorem first_eq_one_of_product {P Q U Z : ℤ} (hP : P ≠ -1)
    (hz : P * Q * U * Z - 1 = 0) : P = 1 := by
  have hm : (Q * U * Z) * P = 1 := by nlinarith only [hz]
  have hu : IsUnit P := IsUnit.of_mul_eq_one_right _ hm
  exact (Int.isUnit_iff.mp hu).resolve_right hP

theorem first_eq_one_of_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : value p v = 0) :
    (ThirteenCarrier.core p v).P = 1 :=
  first_eq_one_of_product (first_ne_neg_one p v hb hv) hz

theorem first_eq_one_of_old_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value71 p v = 0) :
    (ThirteenCarrier.core p v).P = 1 :=
  first_eq_one_of_product (first_ne_neg_one p v hb hv) hz

/-- Identity on all thirteen coordinates, in both directions. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenCarrier.value71 p v = 0 := by
  constructor
  · intro hz
    have hP := first_eq_one_of_zero p v hb hv hz
    simpa only [correction_identity, hP, sub_self, mul_zero, sub_zero] using hz
  · intro hz
    have hP := first_eq_one_of_old_zero p v hb hv hz
    simpa only [correction_identity, hP, sub_self, mul_zero, sub_zero] using hz

theorem value_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 13 → R) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value, correctedStrong, ThirteenCarrier.core, data, Carrier65.core, parent, b,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem positive_polynomial_zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (polynomial p) = 0 ↔
      MvPolynomial.eval v (ThirteenCarrier.polynomial71 p) = 0 := by
  rw [eval_polynomial, ThirteenCarrier.eval_polynomial71]
  exact positive_zero_iff p v hb hv

theorem exists_positive_zero_iff (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenCarrier.polynomial71 p) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · exact ⟨v,hv,(positive_polynomial_zero_iff p v hb hv).mp hz⟩
  · exact ⟨v,hv,(positive_polynomial_zero_iff p v hb hv).mpr hz⟩

attribute [local irreducible] CurrentKernel2011.K

/-- The complete actual2011 four-port tuple, including shifted MF exactly once. -/
noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))

/-- External consistency equivalence at the exact current constants. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  have hb : 0 < CurrentMasks2011.ports (CurrentKernel2011.K : ℤ) 0 := CurrentMasks2011.beta_pos_int
  exact (not_congr (exists_positive_zero_iff _ hb)).trans
    CurrentPositiveZero2011.no_thirteen_positive_zero_iff_conZFC.2.2

end DiophantineConsistency.ThirteenCorrectedStrong
