import DiophantineConsistency.ThirteenSharedSquares96

/-! # Three integer unit squares for the thirteen-coordinate carrier

The new polynomial is generally different from the grouped residual sum.
Its entire positive zero set is identical, with the identity witness map.
The separate literal graph audit establishes 75 operations and degree 96.
-/

set_option Elab.async false
namespace DiophantineConsistency.ThirteenUnitSphere96
open ThirteenCarrierSoundness

variable {A B : Type*} [CommRing A] [CommRing B]

def value (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  (d.P * d.Q)^2 + (ThirteenGroupedSquares96.auxiliary p v)^2 +
    (Carrier65.strong d)^2 - 3

private theorem integer_square_bound (a : ℤ) (h : a^2 ≤ 3) : a^2 ≤ 1 := by
  have hlo : -1 ≤ a := by
    by_contra hn
    have ha : a ≤ -2 := by omega
    nlinarith
  have hhi : a ≤ 1 := by
    by_contra hn
    have ha : 2 ≤ a := by omega
    nlinarith
  interval_cases a <;> norm_num

/-- This is specific to integers: no nonzero-factor premise is needed. -/
theorem three_squares_eq_three_iff (a b c : ℤ) :
    a^2 + b^2 + c^2 = 3 ↔ a^2 = 1 ∧ b^2 = 1 ∧ c^2 = 1 := by
  constructor
  · intro h
    have ha := sq_nonneg a
    have hb := sq_nonneg b
    have hc := sq_nonneg c
    have ha' := integer_square_bound a (by omega)
    have hb' := integer_square_bound b (by omega)
    have hc' := integer_square_bound c (by omega)
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨ha,hb,hc⟩; omega

theorem product_ne_neg_one (P Q : ℤ) (hP : P ≠ -1) (hQ : Q ≠ -1) :
    P*Q ≠ -1 := by
  intro h
  have hu : IsUnit P := IsUnit.of_mul_eq_one_right (-Q) (by nlinarith only [h])
  have hp : P = 1 := (Int.isUnit_iff.mp hu).resolve_right hP
  exact hQ (by simpa only [hp, one_mul] using h)

theorem main_ne_neg_one (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    (data p v).Q ≠ -1 := by
  change (data p v).D^2 - (data p v).delta * (data p v).c^2 ≠ -1
  rw [show (data p v).delta = ((data p v).a+2)^2-1 from
    Carrier65.delta_shape p (parent p v 1 1)]
  exact ShortEquation.strong_ne_neg_one _ _ _

theorem strong_ne_neg_one (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    Carrier65.strong (data p v) ≠ -1 := by
  unfold Carrier65.strong
  rw [show (data p v).delta = ((data p v).a+2)^2-1 from
    Carrier65.delta_shape p (parent p v 1 1)]
  exact ShortEquation.strong_ne_neg_one _ _ _

/-- The auxiliary exclusion is used only after recovering the strong unit. -/
theorem auxiliary_ne_neg_one (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hs : Carrier65.strong (data p v) = 1) :
    ThirteenGroupedSquares96.auxiliary p v ≠ -1 := by
  let d := data p v
  have hf : d.f^2 - 1 = d.delta * (d.i*d.c^2)^2 := by
    change d.f^2 - d.delta*(d.i*d.c^2)^2 = 1 at hs
    linarith only [hs]
  have hc : d.delta*(d.f^2-1) = d.S^2 := by
    rw [hf]
    change d.delta*(d.delta*(d.i*d.c^2)^2) = (d.i*d.delta*d.c^2)^2
    ring
  change d.delta*(d.f^2-1)*(d.V^2-(ThirteenLVCarrier.y p v)^2) +
    (ThirteenLVCarrier.y p v)^2 ≠ -1
  rw [hc]
  exact ShortSystem.square_aux_ne_neg_one _ _ _

theorem positive_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ (data p v).P*(data p v).Q = 1 ∧
      ThirteenGroupedSquares96.auxiliary p v = 1 ∧
      Carrier65.strong (data p v) = 1 := by
  constructor
  · intro hz
    have he : ((data p v).P*(data p v).Q)^2 +
        (ThirteenGroupedSquares96.auxiliary p v)^2 +
        (Carrier65.strong (data p v))^2 = 3 := by
      change _ - 3 = 0 at hz
      linarith only [hz]
    obtain ⟨hp,hu,hs⟩ := (three_squares_eq_three_iff _ _ _).mp he
    have hP : (data p v).P ≠ -1 :=
      ThirteenCorrectedStrong.first_ne_neg_one p v hb hv
    have hp1 := (sq_eq_one_iff.mp hp).resolve_right
      (product_ne_neg_one _ _ hP (main_ne_neg_one p v))
    have hs1 := (sq_eq_one_iff.mp hs).resolve_right (strong_ne_neg_one p v)
    have hu1 := (sq_eq_one_iff.mp hu).resolve_right (auxiliary_ne_neg_one p v hs1)
    exact ⟨hp1,hu1,hs1⟩
  · rintro ⟨hp,hu,hs⟩
    simp only [value,hp,hu,hs]
    norm_num

/-- Both directions use the same thirteen positive coordinates. -/
theorem positive_zero_iff72 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenLVCarrier.value72 p v = 0 := by
  rw [positive_zero_iff_residuals p v hb hv,
    ← ThirteenGroupedSquares96.value_zero_iff_residuals]
  exact ThirteenGroupedSquares96.positive_zero_iff72 p v hb hv

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value, ThirteenGroupedSquares96.auxiliary, ThirteenLVCarrier.y,
    ThirteenLVCarrier.L, G, data, Carrier65.core, parent, b, Carrier65.strong,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem exists_positive_zero_iff72 (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenLVCarrier.polynomial72 p) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · rw [eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [ThirteenLVCarrier.eval_polynomial72]
    exact (positive_zero_iff72 p v hb hv).mp hz
  · rw [ThirteenLVCarrier.eval_polynomial72] at hz
    refine ⟨v,hv,?_⟩
    rw [eval_polynomial]
    exact (positive_zero_iff72 p v hb hv).mpr hz

noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial CurrentWindowCarry2011.ports

/-- External Lean equivalence for actual ports and actual ConZFC; not an
internal HA, PA, or ZFC derivation. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  exact (not_congr (exists_positive_zero_iff72 _ hb)).trans
    ThirteenLVCarrier.no_current_positive72_zero_iff_conZFC

end DiophantineConsistency.ThirteenUnitSphere96
