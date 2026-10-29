import DiophantineConsistency.ThirteenUnitSphere96

/-! # A first-norm correction of the thirteen-coordinate unit sphere

The correction vanishes on either entire positive zero set. Its purpose is
polynomial degree cancellation, not a change in witnesses or fixed ports.
The separate literal graph audit pays84 operations and proves degree92.
-/

set_option Elab.async false
namespace DiophantineConsistency.ThirteenFirstNormCorrection92
open ThirteenCarrierSoundness

variable {A B : Type*} [CommRing A] [CommRing B]

def coefficient (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  16 * ((b p v * v 5 * G p v * (data p v).V)^2 * (data p v).f^2)

def auxiliary (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  ThirteenGroupedSquares96.auxiliary p v - coefficient p v * ((data p v).P - 1)

def value (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  (d.P*d.Q)^2 + (auxiliary p v)^2 + (Carrier65.strong d)^2 - 3

/-- Only the first two negative-unit exclusions are required. The coefficient
and both other sphere coordinates are arbitrary integers. -/
theorem correction_zero_iff (P Q U Z c : ℤ) (hP : P ≠ -1) (hQ : Q ≠ -1) :
    (P*Q)^2 + (U-c*(P-1))^2 + Z^2 - 3 = 0 ↔
      (P*Q)^2 + U^2 + Z^2 - 3 = 0 := by
  have first_unit (u : ℤ) (h : (P*Q)^2+u^2+Z^2-3=0) : P = 1 := by
    have he : (P*Q)^2+u^2+Z^2=3 := by linarith only [h]
    have hs := (ThirteenUnitSphere96.three_squares_eq_three_iff _ _ _).mp he
    have hpq : P*Q=1 := (sq_eq_one_iff.mp hs.1).resolve_right
      (ThirteenUnitSphere96.product_ne_neg_one P Q hP hQ)
    have hu : IsUnit P := IsUnit.of_mul_eq_one_right Q (by simpa only [mul_comm] using hpq)
    exact (Int.isUnit_iff.mp hu).resolve_right hP
  constructor <;> intro h
  · have hp := first_unit (U-c*(P-1)) h
    simpa only [hp, sub_self, mul_zero, sub_zero] using h
  · have hp := first_unit U h
    simpa only [hp, sub_self, mul_zero, sub_zero] using h

/-- Both directions retain every positive coordinate unchanged. -/
theorem positive_zero_iff75 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenUnitSphere96.value p v = 0 := by
  exact correction_zero_iff _ _ _ _ _
    (ThirteenCorrectedStrong.first_ne_neg_one p v hb hv)
    (ThirteenUnitSphere96.main_ne_neg_one p v)

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value, auxiliary, coefficient, ThirteenGroupedSquares96.auxiliary,
    ThirteenLVCarrier.y, ThirteenLVCarrier.L, G, data, Carrier65.core,
    parent, b, Carrier65.strong, map_add, map_sub, map_mul, map_pow, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem exists_positive_zero_iff75 (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenUnitSphere96.polynomial p) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · rw [eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [ThirteenUnitSphere96.eval_polynomial]
    exact (positive_zero_iff75 p v hb hv).mp hz
  · rw [ThirteenUnitSphere96.eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [eval_polynomial]
    exact (positive_zero_iff75 p v hb hv).mpr hz

noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial CurrentWindowCarry2011.ports

/-- External Lean equivalence with the actual ConZFC predicate. This does
not assert an internal HA, PA, or ZFC proof or global size minimality. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := CurrentMasks2011.beta_pos_int
  exact (not_congr (exists_positive_zero_iff75 _ hb)).trans
    ThirteenUnitSphere96.no_current_positive_zero_iff_conZFC

end DiophantineConsistency.ThirteenFirstNormCorrection92
