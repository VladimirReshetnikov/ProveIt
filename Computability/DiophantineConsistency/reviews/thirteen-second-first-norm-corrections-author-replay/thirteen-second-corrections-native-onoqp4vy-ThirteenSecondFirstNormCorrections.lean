import DiophantineConsistency.ThirteenFirstNormCorrection92

/-! Two further first-norm corrections preserve the entire positive zero set.
The separate literal graph audit pays 92/97 operations and proves degrees90/88.
No polynomial-equality, internal consistency proof, or optimality is asserted. -/
set_option Elab.async false
namespace DiophantineConsistency.ThirteenSecondFirstNormCorrections
open ThirteenCarrierSoundness
variable {A B : Type*} [CommRing A] [CommRing B]

def coefficient90 (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  let W := b p v * v 5 * G p v * d.V
  16 * W * (W * (d.f^2-1) + 2*d.f^2*v 5*(d.V*d.C-b p v*G p v*d.f^2*d.R))

def coefficient88 (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  let BG := b p v * G p v
  16 * (v 5)^2 * d.V * (BG^2*d.V*(d.f^2-1) +
    2*d.f^2*(d.V*d.C*(2*BG-d.X*d.C)-BG^2*d.f^2*d.R))

/-- Exact coefficient refactoring; all products are paid in the literal graph. -/
theorem coefficient88_eq_difference (p : Fin 4 → A) (v : Fin 13 → A) :
    coefficient88 p v = coefficient90 p v -
      32*(data p v).f^2*(v 5)^2*(data p v).V^2*(data p v).C *
        ((data p v).X*(data p v).C-b p v*G p v) := by
  simp only [coefficient88, coefficient90]
  ring

/-- False selects the 92-operation degree90 graph; true selects 97/88. -/
def coefficient (sharp : Bool) (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  if sharp then coefficient88 p v else coefficient90 p v

def auxiliary (sharp : Bool) (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  ThirteenGroupedSquares96.auxiliary p v - coefficient sharp p v * ((data p v).P-1)

def value (sharp : Bool) (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  (d.P*d.Q)^2 + (auxiliary sharp p v)^2 + (Carrier65.strong d)^2 - 3

/-- Either zero independently forces P=1; the correction then vanishes.
Both maps are the identity on every positive coordinate. -/
theorem positive_zero_iff75 (sharp : Bool) (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value sharp p v=0 ↔ ThirteenUnitSphere96.value p v=0 :=
  ThirteenFirstNormCorrection92.correction_zero_iff _ _ _ _ _
    (ThirteenCorrectedStrong.first_ne_neg_one p v hb hv)
    (ThirteenUnitSphere96.main_ne_neg_one p v)

theorem both_positive_zero_sets (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value false p v=0 ↔ value true p v=0 :=
  (positive_zero_iff75 false p v hb hv).trans (positive_zero_iff75 true p v hb hv).symm

theorem value_map (sharp : Bool) (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value sharp p v) = value sharp (fun j => φ (p j)) (fun j => φ (v j)) := by
  cases sharp <;> simp [value, auxiliary, coefficient, coefficient90, coefficient88,
    ThirteenGroupedSquares96.auxiliary, ThirteenLVCarrier.y, ThirteenLVCarrier.L,
    G, data, Carrier65.core, parent, b, Carrier65.strong,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

noncomputable def polynomial (sharp : Bool) (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value sharp (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (sharp : Bool) (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial sharp p) = value sharp p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map sharp (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem exists_positive_zero_iff75 (sharp : Bool) (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial sharp p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenUnitSphere96.polynomial p) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · rw [eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [ThirteenUnitSphere96.eval_polynomial]
    exact (positive_zero_iff75 sharp p v hb hv).mp hz
  · rw [ThirteenUnitSphere96.eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [eval_polynomial]
    exact (positive_zero_iff75 sharp p v hb hv).mpr hz

noncomputable def currentPolynomial (sharp : Bool) : MvPolynomial (Fin 13) ℤ :=
  polynomial sharp CurrentWindowCarry2011.ports

/-- External Lean equivalence for each actual current tuple. -/
theorem no_current_positive_zero_iff_conZFC (sharp : Bool) :
    (¬ CurrentCarrierArithmetic2011.PositiveZero (currentPolynomial sharp)) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  exact (not_congr (exists_positive_zero_iff75 sharp _ hb)).trans
    ThirteenUnitSphere96.no_current_positive_zero_iff_conZFC

end DiophantineConsistency.ThirteenSecondFirstNormCorrections
