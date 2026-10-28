import DiophantineConsistency.CarrierScaledAuxiliary118

set_option autoImplicit false
set_option Elab.async false

/-! The fourteen-coordinate normalized scaled product. The identity on all
positive inputs preserves its entire zero set; the separate complete graph
establishes67 integer-leaf operations and degree106 at current2011 ports. -/
namespace DiophantineConsistency.CarrierNormalizedProduct106
open Carrier65

variable {A B : Type*} [CommRing A] [CommRing B]

def auxiliary (d : Core A) : A := d.delta*(d.f^2-1)*(d.V^2-d.y^2)+d.y^2

def value (p : Fin 4 → A) (v : Fin 14 → A) : A :=
  let d := core p v
  d.P*d.Q*auxiliary d*d.W*strong d-1

/-- A polynomial identity over every commutative ring; no zero is assumed. -/
theorem scaled_identity (p : Fin 4 → A) (v : Fin 14 → A) :
    CarrierScaledAuxiliary118.value p v=(core p v).delta*value p v := by
  dsimp only [CarrierScaledAuxiliary118.value,value,auxiliary]
  rw [strong_scale]
  ring

/-- Cancellation occurs in the proof, not as a division in the polynomial. -/
theorem zero_iff_scaled (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hd : (core p v).delta ≠ 0) :
    value p v=0 ↔ CarrierScaledAuxiliary118.value p v=0 := by
  rw [scaled_identity,mul_eq_zero]
  simp only [hd,false_or]

theorem positive_zero_iff_original (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j,0 < v j) : value p v=0 ↔ Carrier65.value p v=0 :=
  (zero_iff_scaled p v (ne_of_gt (delta_pos p v hb hv))).trans
    (CarrierScaledAuxiliary118.positive_zero_sets p v hb hv)

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 14 → A) :
    φ (value p v)=value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value,auxiliary,strong,core,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 14) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    MvPolynomial.eval v (polynomial p)=value p v := by
  simpa only [polynomial,MvPolynomial.eval_C,MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem positive_polynomial_zero_iff_original (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j,0 < v j) :
    MvPolynomial.eval v (polynomial p)=0 ↔ MvPolynomial.eval v (Carrier65.polynomial p)=0 := by
  rw [eval_polynomial,Carrier65.eval_polynomial]
  exact positive_zero_iff_original p v hb hv

noncomputable def currentPolynomial : MvPolynomial (Fin 14) ℤ :=
  polynomial CurrentWindowCarry2011.ports

theorem current_positive_zero_iff :
    CurrentCarrierArithmetic2011.PositiveZero currentPolynomial ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  constructor <;> rintro ⟨v,hv,hz⟩ <;> refine ⟨v,hv,?_⟩
  · exact (positive_polynomial_zero_iff_original _ v hb hv).mp hz
  · exact (positive_polynomial_zero_iff_original _ v hb hv).mpr hz

/-- External exact-current-tuple endpoint, not an internal HA or ZFC proof. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔ DiophantineConsistency.ConZFC :=
  (not_congr current_positive_zero_iff).trans CurrentPositiveZero2011.no_positive_zero_iff_conZFC

end DiophantineConsistency.CarrierNormalizedProduct106
