import DiophantineConsistency.CurrentPositiveZero2011

/-! The accepted scaled-auxiliary replacement, now bound to the actual
fourteen-coordinate carrier and current ports. The identity on positive
coordinates preserves the entire zero set, including noncanonical zeros.
The separate finite graph records the 66-operation/degree-118 profile;
this packet proves the algebraic and external consistency transfer. -/

namespace DiophantineConsistency.CarrierScaledAuxiliary118

open Carrier65

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

variable {A B : Type*} [CommRing A] [CommRing B]

/-- One extra subtraction reuses the live producer delta*f². -/
def value (p : Fin 4 → A) (v : Fin 14 → A) : A :=
  let b := core p v
  b.P*b.Q*((b.delta*b.f^2-b.delta)*(b.V^2-b.y^2)+b.y^2)*b.W*b.Z-b.delta

theorem scaled_identity (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    value p v = (core p v).delta * ShortEquation.product
      ((core p v).P*(core p v).Q*(core p v).W)
      ((core p v).delta*((core p v).f^2-1))
      ((core p v).V^2-(core p v).y^2) (core p v).y (strong (core p v)) := by
  dsimp only [value, ShortEquation.product]
  rw [strong_scale]
  ring

theorem original_scaled_identity (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    Carrier65.value p v = (core p v).delta * ShortEquation.product
      ((core p v).P*(core p v).Q*(core p v).W)
      ((core p v).delta^2*((core p v).i*(core p v).c^2)^2)
      ((core p v).V^2-(core p v).y^2) (core p v).y (strong (core p v)) := by
  have hU : (core p v).U =
      (core p v).delta^2*((core p v).i*(core p v).c^2)^2*
        ((core p v).V^2-(core p v).y^2)+(core p v).y^2 := by
    change ((core p v).i*(core p v).delta*(core p v).c^2)^2*
      ((core p v).V^2-(core p v).y^2)+(core p v).y^2 = _
    ring
  rw [Carrier65.scaled_identity, hU]
  unfold ShortEquation.product
  ring

/-- Only a nonzero discriminant is needed; no existing zero is supplied. -/
theorem value_zero_iff_original (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hd : (core p v).delta ≠ 0) : value p v=0 ↔ Carrier65.value p v=0 := by
  have hn : (core p v).f^2-(core p v).delta*((core p v).i*(core p v).c^2)^2 ≠ -1 := by
    rw [delta_shape]
    exact ShortEquation.strong_ne_neg_one _ _ _
  rw [scaled_identity, original_scaled_identity]
  simp only [mul_eq_zero, hd, false_or]
  exact (ShortEquation.replace_coefficient hn).symm

theorem positive_zero_sets (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0<p 0) (hv : ∀ j,0<v j) : value p v=0 ↔ Carrier65.value p v=0 :=
  value_zero_iff_original p v (ne_of_gt (delta_pos p v hb hv))

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 14 → A) :
    φ (value p v)=value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value, core, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 14) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    MvPolynomial.eval v (polynomial p)=value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem positive_polynomial_zero_sets (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0<p 0) (hv : ∀ j,0<v j) :
    MvPolynomial.eval v (polynomial p)=0 ↔
      MvPolynomial.eval v (Carrier65.polynomial p)=0 := by
  rw [eval_polynomial, Carrier65.eval_polynomial]
  exact positive_zero_sets p v hb hv

noncomputable def currentPolynomial : MvPolynomial (Fin 14) ℤ :=
  polynomial CurrentWindowCarry2011.ports

/-- The literal current fixed ports, with the same fourteen positive inputs. -/
theorem current_positive_zero_iff :
    CurrentCarrierArithmetic2011.PositiveZero currentPolynomial ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  have hb : (0 : ℤ)<CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ)<CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  constructor <;> rintro ⟨v,hv,hz⟩ <;> refine ⟨v,hv,?_⟩
  · exact (positive_polynomial_zero_sets _ v hb hv).mp hz
  · exact (positive_polynomial_zero_sets _ v hb hv).mpr hz

theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC :=
  (not_congr current_positive_zero_iff).trans CurrentPositiveZero2011.no_positive_zero_iff_conZFC

end DiophantineConsistency.CarrierScaledAuxiliary118
