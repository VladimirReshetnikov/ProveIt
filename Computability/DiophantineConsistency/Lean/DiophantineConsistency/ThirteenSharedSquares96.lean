import DiophantineConsistency.ThirteenGroupedSquares96

/-! # Sharing the strong residual's `f² - 1`

The same subtraction supplies the auxiliary coefficient and the strong
residual. This is an exact polynomial identity over every commutative ring;
the positive zero set, all coordinates, and all four ports are unchanged.
The separate literal graph auditor establishes 76 operations and degree 96.
-/

set_option Elab.async false
namespace DiophantineConsistency.ThirteenSharedSquares96
open ThirteenCarrierSoundness

variable {A B : Type*} [CommRing A] [CommRing B]

def value (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  let y := ThirteenLVCarrier.y p v
  let h := d.f^2 - 1
  let u := d.delta * h * (d.V^2 - y^2) + y^2
  let z := h - d.delta * (d.i * d.c^2)^2
  (d.P * d.Q - 1)^2 + (u - 1)^2 + z^2

/-- Sharing a subtraction does not require positivity or a norm premise. -/
theorem value_eq_grouped (p : Fin 4 → A) (v : Fin 13 → A) :
    value p v = ThirteenGroupedSquares96.value p v := by
  simp only [value, ThirteenGroupedSquares96.value,
    ThirteenGroupedSquares96.auxiliary, Carrier65.strong]
  ring

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value_eq_grouped, ThirteenGroupedSquares96.value_map]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem polynomial_eq_grouped (p : Fin 4 → ℤ) :
    polynomial p = ThirteenGroupedSquares96.polynomial p :=
  value_eq_grouped _ _

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  rw [polynomial_eq_grouped, ThirteenGroupedSquares96.eval_polynomial, value_eq_grouped]

/-- Both witness maps are the identity, on all assignments, including signed ones. -/
theorem same_assignment (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p) = 0 ↔
      MvPolynomial.eval v (ThirteenGroupedSquares96.polynomial p) = 0 := by
  rw [polynomial_eq_grouped]

theorem positive_zero_iff72 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenLVCarrier.value72 p v = 0 := by
  rw [value_eq_grouped]
  exact ThirteenGroupedSquares96.positive_zero_iff72 p v hb hv

noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial CurrentWindowCarry2011.ports

theorem currentPolynomial_eq_grouped :
    currentPolynomial = ThirteenGroupedSquares96.currentPolynomial :=
  polynomial_eq_grouped _

/-- External Lean equivalence for the actual current ports and actual ConZFC.
This does not assert an internal HA, PA, or ZFC derivation. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  rw [currentPolynomial_eq_grouped]
  exact ThirteenGroupedSquares96.no_current_positive_zero_iff_conZFC

end DiophantineConsistency.ThirteenSharedSquares96
