import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
import DiophantineConsistency.ArithmeticSquareDivisibility

/-! The actual adaptive scaled norms supply their own integral quotients.
The signed roots are retained through their natural magnitudes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticSquareDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact cancellation of a positive scale from a square identity. -/
theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n) :
    ∃ t : V, z=m*t ∧ t*t=n := by
  have hd : m*m ∣ z*z := ⟨n,h⟩
  obtain ⟨t,ht⟩ := dvd_of_square_dvd m z hm hd
  refine ⟨t,ht,?_⟩
  apply mul_left_cancel₀ (ne_of_gt (mul_pos hm hm))
  calc
    (m*m)*(t*t)=(m*t)*(m*t) := by ring
    _=z*z := by rw [ht]
    _=(m*m)*n := h

def Quotients (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let U : V := v 7*(q*q)
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let delta : V := (3+4*a)+a*a
  ∃ first main : V, 0<first ∧ 0<main ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v) = M*first ∧
    first*first=1+ell*(ell+k) ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v) = U*main ∧
    main*main=1+delta*(c*c)

/-- Neither quotient nor its positive sign is supplied by the caller. -/
theorem quotients_of_scaled_norms (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))
    (hU : 0<v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))
    (h : ScaledNorms p v) : Quotients p v := by
  dsimp only [ScaledNorms] at h
  dsimp only [Quotients]
  obtain ⟨first,hfirst,hfn⟩ := scaled_quotient _ _ _ hM h.1
  obtain ⟨main,hmain,hmn⟩ := scaled_quotient _ _ _ hU h.2
  have hf : 0<first := pos_of_mul_pos_left (by rw [hfn]; simp) (by simp)
  have hg : 0<main := pos_of_mul_pos_left (by rw [hmn]; simp) (by simp)
  exact ⟨first,main,hf,hg,hfirst,hfn,hmain,hmn⟩

theorem expressionAt_quotients (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : Quotients p v := by
  have hp := scaled_parameters_positive p v hb hv
  exact quotients_of_scaled_norms p v hp.2.1 hp.2.2.1
    (expressionAt_concrete_scaled_norms p v hz)

theorem current_quotients (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : Quotients currentPorts v := by
  have hp := current_parameters_positive v hv
  apply quotients_of_scaled_norms currentPorts v _ _ (current_scaled_norms v hz)
  · simpa only [currentPorts,Matrix.cons_val_zero] using hp.2.1
  · simpa only [currentPorts,Matrix.cons_val_zero] using hp.2.2.1

theorem current_natural_quotients (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Quotients currentPorts (fun j => v j+1) :=
  current_quotients _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveQuotients2011
