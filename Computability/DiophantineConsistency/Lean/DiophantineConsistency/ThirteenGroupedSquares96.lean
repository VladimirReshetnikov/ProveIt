import DiophantineConsistency.ThirteenLVCarrier

/-! # Three grouped square residuals of the normalized mixed carrier

This polynomial uses the same thirteen positive variables and four fixed ports
as the 72-operation mixed carrier.  Its positive zero set is identical, with
the identity witness map.  The literal graph and its degree are audited in the
separate finite packet; this module proves the complete zero-set equivalence.
-/

set_option Elab.async false
set_option maxRecDepth 10000
namespace DiophantineConsistency.ThirteenGroupedSquares96
open ThirteenCarrierSoundness

variable {A B : Type*} [CommRing A] [CommRing B]

def auxiliary (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  let y := ThirteenLVCarrier.y p v
  d.delta * (d.f^2 - 1) * (d.V^2 - y^2) + y^2

def value (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  (d.P * d.Q - 1)^2 + (auxiliary p v - 1)^2 + (Carrier65.strong d - 1)^2

/-- No positivity assumption is needed for the square-residual implication. -/
theorem three_squares_zero_iff (a b c : ℤ) :
    a^2 + b^2 + c^2 = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have ha := sq_nonneg a
    have hb := sq_nonneg b
    have hc := sq_nonneg c
    have ha0 : a^2 = 0 := by omega
    have hb0 : b^2 = 0 := by omega
    have hc0 : c^2 = 0 := by omega
    exact ⟨by nlinarith only [ha0], by nlinarith only [hb0], by nlinarith only [hc0]⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

theorem value_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    value p v = 0 ↔ (data p v).P * (data p v).Q = 1 ∧
      auxiliary p v = 1 ∧ Carrier65.strong (data p v) = 1 := by
  unfold value
  rw [three_squares_zero_iff]
  simp only [sub_eq_zero]

/-- The accepted entire-positive-zero theorem supplies the strong norm.  It
also supplies the auxiliary Pell norm, which becomes the literal auxiliary
factor after substituting that strong norm.  P and Q need not be separated. -/
theorem residuals_of_positive72_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j)
    (hz : ThirteenLVCarrier.value72 p v = 0) :
    (data p v).P * (data p v).Q = 1 ∧ auxiliary p v = 1 ∧
      Carrier65.strong (data p v) = 1 := by
  have hnormal : ThirteenLVCarrier.normalValue p v (ThirteenLVCarrier.y p v) = 0 :=
    (ThirteenLVCarrier.positive_zero_iff72 p v hb hv).mpr hz
  obtain ⟨hs, hn⟩ := ThirteenLVCarrier.norms_of_zero p v
    (ThirteenLVCarrier.y p v) hb hv hnormal
  let d := data p v
  have hs' : d.f^2 - 1 = d.delta * (d.i * d.c^2)^2 := by
    change d.f^2 - d.delta * (d.i * d.c^2)^2 = 1 at hs
    linarith only [hs]
  have hc : d.delta * (d.f^2 - 1) = d.S^2 := by
    rw [hs']
    change d.delta * (d.delta * (d.i * d.c^2)^2) = (d.i * d.delta * d.c^2)^2
    ring
  have hu : auxiliary p v = 1 := by
    change d.delta * (d.f^2 - 1) * (d.V^2 - (ThirteenLVCarrier.y p v)^2) +
      (ThirteenLVCarrier.y p v)^2 = 1
    rw [hc]
    nlinarith only [hn]
  have hproduct : (data p v).P * (data p v).Q = 1 := by
    change (data p v).P * (data p v).Q * auxiliary p v *
      Carrier65.strong (data p v) - 1 = 0 at hz
    rw [hu, hs] at hz
    simpa using sub_eq_zero.mp hz
  exact ⟨hproduct, hu, hs⟩

theorem positive_zero_iff72 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenLVCarrier.value72 p v = 0 := by
  constructor
  · intro hz
    obtain ⟨hp, hu, hs⟩ := (value_zero_iff_residuals p v).mp hz
    change (data p v).P * (data p v).Q * auxiliary p v *
      Carrier65.strong (data p v) - 1 = 0
    rw [hp, hu, hs]; norm_num
  · intro hz
    exact (value_zero_iff_residuals p v).mpr
      (residuals_of_positive72_zero p v hb hv hz)

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value, auxiliary, ThirteenLVCarrier.y, ThirteenLVCarrier.L, G, data,
    Carrier65.core, parent, b, Carrier65.strong,
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
  constructor <;> rintro ⟨v, hv, hz⟩
  · rw [eval_polynomial] at hz
    refine ⟨v, hv, ?_⟩
    rw [ThirteenLVCarrier.eval_polynomial72]
    exact (positive_zero_iff72 p v hb hv).mp hz
  · rw [ThirteenLVCarrier.eval_polynomial72] at hz
    refine ⟨v, hv, ?_⟩
    rw [eval_polynomial]
    exact (positive_zero_iff72 p v hb hv).mpr hz

noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial CurrentWindowCarry2011.ports

/-- An external Lean theorem using the actual DiophantineConsistency.ConZFC
definition. This is not an internal HA, PA, or ZFC derivation. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  exact (not_congr (exists_positive_zero_iff72 _ hb)).trans
    ThirteenLVCarrier.no_current_positive72_zero_iff_conZFC

end DiophantineConsistency.ThirteenGroupedSquares96
