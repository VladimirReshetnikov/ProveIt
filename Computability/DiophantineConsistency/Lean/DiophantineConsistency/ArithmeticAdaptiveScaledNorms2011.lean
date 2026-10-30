import DiophantineConsistency.ArithmeticSignedPairExpressions
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Literal first and main adaptive scaled norms from the actual split zero.
Signed roots are represented by natural pairs. No quotient is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
open ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Select the root in the literal `1+(root*root-rhs)` factor shape. -/
def rootTerm {σ : Type*} : Expr σ → Expr σ
  | .add _ (.sub (.mul z _) _) => z
  | _ => .constant 0

def rightTerm {σ : Type*} : Expr σ → Expr σ
  | .add _ (.sub _ rhs) => rhs
  | _ => .constant 0

theorem first_shape (p : Fin 4 → ℤ) :
    (factors p).1 = 1 + (rootTerm (factors p).1 * rootTerm (factors p).1 - rightTerm (factors p).1) := rfl

theorem main_shape (p : Fin 4 → ℤ) :
    (factors p).2.1 = 1 + (rootTerm (factors p).2.1 * rootTerm (factors p).2.1 - rightTerm (factors p).2.1) := rfl

/-- A positive signed unit of the displayed square-minus-right factor forces
an equality of its actual natural split, with no sign of the root assumed. -/
theorem unit_square_norm {σ : Type*} (z rhs : Expr σ) (v : σ → V)
    (hu : (pairEval (1+(z*z-rhs)) v).1 = (pairEval (1+(z*z-rhs)) v).2+1) :
    magnitude (pairEval z v)*magnitude (pairEval z v) + (pairEval rhs v).2 =
      (pairEval rhs v).1 := by
  change (pairEval (Expr.add (Expr.constant 1) (Expr.sub (Expr.mul z z) rhs)) v).1 =
    (pairEval (Expr.add (Expr.constant 1) (Expr.sub (Expr.mul z z) rhs)) v).2+1 at hu
  have hp : Equivalent (multiply (pairEval z v) (pairEval z v)) (pairEval rhs v) := by
    have h : 1+((multiply (pairEval z v) (pairEval z v)).1+(pairEval rhs v).2) =
        1+((multiply (pairEval z v) (pairEval z v)).2+(pairEval rhs v).1) := by
      simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,multiply,add_assoc,add_comm,add_left_comm]
        using hu
    exact add_left_cancel h
  have h := equivalent_trans (equivalent_symm (square_magnitude (pairEval z v))) hp
  simpa [Equivalent,natural] using h

/-- Both scaled equations follow from the actual arbitrary-port split zero. -/
theorem expressionAt_scaled_norms (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt p) v) :
    magnitude (pairEval (rootTerm (factors p).1) v)*magnitude (pairEval (rootTerm (factors p).1) v) +
        (pairEval (rightTerm (factors p).1) v).2 = (pairEval (rightTerm (factors p).1) v).1 ∧
    magnitude (pairEval (rootTerm (factors p).2.1) v)*magnitude (pairEval (rootTerm (factors p).2.1) v) +
        (pairEval (rightTerm (factors p).2.1) v).2 = (pairEval (rightTerm (factors p).2.1) v).1 := by
  obtain ⟨h0,h1,_,_⟩ := expressionAt_factor_units p v hz
  rw [first_shape p] at h0
  rw [main_shape p] at h1
  exact ⟨unit_square_norm _ _ _ h0,unit_square_norm _ _ _ h1⟩

/-- The first and main right-hand sides are positive-syntax polynomials; no
truncated subtraction occurs in their evaluation. -/
theorem first_rhs_pair (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    pairEval (rightTerm (factors (fun j => (p j:ℤ))).1) v =
      (M*M*(1+ell*(ell+k)),0) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eM : Expr (Fin 13) := .mul (.mul eQ (.mul eQ eQ)) eB
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eL : Expr (Fin 13) := .mul (.mul (.var 6) (.var 7)) (.mul (.var 7) eK)
  change pairEval (.mul (.mul eM eM) (.add (.constant 1) (.mul eL (.add eL eK)))) v = _
  simp [eB,eQ,eM,eK,eL,pairEval,Expr.splitNatural,NatExpr.evalSemiring]

theorem main_rhs_pair (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let delta : V := (3+4*a)+a*a
    pairEval (rightTerm (factors (fun j => (p j:ℤ))).2.1) v =
      (U*U*(1+delta*(c*c)),0) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eU : Expr (Fin 13) := .mul (.var 7) (.mul eQ eQ)
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add (.mul (.var 6) (.var 7)) (.var 7)
  let eD : Expr (Fin 13) := .add (.add (.constant 3) (.mul (.constant 4) eA)) (.mul eA eA)
  change pairEval (.mul (.mul eU eU) (.add (.constant 1) (.mul eD (.mul eC eC)))) v = _
  simp [eB,eQ,eU,eK,eC,eA,eD,pairEval,Expr.splitNatural,NatExpr.evalSemiring]

/-- These actual scaled Pell equalities retain the possibly signed roots. -/
theorem expressionAt_concrete_scaled_norms (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let delta : V := (3+4*a)+a*a
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)*
      magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v) = M*M*(1+ell*(ell+k)) ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v)*
      magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v) = U*U*(1+delta*(c*c)) := by
  have h := expressionAt_scaled_norms (fun j => (p j:ℤ)) v hz
  rw [first_rhs_pair p v,main_rhs_pair p v] at h
  simpa only [Prod.fst,Prod.snd,add_zero] using h

def ScaledNorms (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let delta : V := (3+4*a)+a*a
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)*
      magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v) = M*M*(1+ell*(ell+k)) ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v)*
      magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v) = U*U*(1+delta*(c*c))

def currentPorts : Fin 4 → ℕ := ![CurrentMasks2011.beta,CurrentKernel2011.K,
  CurrentMasks2011.lowPort,CurrentMasks2011.highPort+CurrentMasks2011.beta]

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

private theorem vector_cast (beta K MC high : ℕ) :
    (fun j => ((![beta,K,MC,high+beta] : Fin 4 → ℕ) j : ℤ)) =
      ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)] := by
  funext j
  fin_cases j <;> simp [Nat.cast_add]

theorem currentPorts_cast : (fun j => (currentPorts j:ℤ)) = CurrentWindowCarry2011.ports :=
  vector_cast CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort CurrentMasks2011.highPort

theorem current_scaled_norms (v : Fin 13 → V) (hz : InternalZero expression v) :
    ScaledNorms currentPorts v := by
  apply expressionAt_concrete_scaled_norms currentPorts v
  rw [currentPorts_cast]
  exact hz

theorem current_natural_scaled_norms (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ScaledNorms currentPorts (fun j => v j+1) :=
  current_scaled_norms _ ((internalZero_positiveShift expression v).mp hz)

/-- The actual scalar multipliers and both first-norm parameters are positive
when the original coordinates and first port are positive. -/
theorem scaled_parameters_positive (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    1<q ∧ 0<M ∧ 0<U ∧ 0<k ∧ 0<ell := by
  dsimp only
  have hb0 : 0<v 0*(p 0:V) := mul_pos (hv 0) hb
  have hq : 0<1+v 0*(p 0:V) := add_pos_of_pos_of_nonneg (by simp) (by simp)
  have hk : 0<v 9+v 10 := add_pos (hv 9) (hv 10)
  exact ⟨lt_add_of_pos_right _ hb0,mul_pos (mul_pos hq (mul_pos hq hq)) hb0,
    mul_pos (hv 7) (mul_pos hq hq),hk,mul_pos (mul_pos (hv 6) (hv 7)) (mul_pos (hv 7) hk)⟩

private theorem beta_positive_nat : 0 < CurrentMasks2011.beta := by
  have hr : 1 < CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1 < CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_parameters_positive (v : Fin 13 → V) (hv : ∀j,0<v j) :
    let q : V := 1+v 0*(CurrentMasks2011.beta:V)
    let M : V := (q*(q*q))*(v 0*(CurrentMasks2011.beta:V))
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    1<q ∧ 0<M ∧ 0<U ∧ 0<k ∧ 0<ell := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  simpa only [currentPorts,Matrix.cons_val_zero] using scaled_parameters_positive currentPorts v hp hv

theorem current_natural_parameters_positive (v : Fin 13 → V) :
    let w := fun j => v j+1
    let q : V := 1+w 0*(CurrentMasks2011.beta:V)
    let M : V := (q*(q*q))*(w 0*(CurrentMasks2011.beta:V))
    let U : V := w 7*(q*q)
    let k : V := w 9+w 10
    let ell : V := (w 6*w 7)*(w 7*k)
    1<q ∧ 0<M ∧ 0<U ∧ 0<k ∧ 0<ell :=
  current_parameters_positive _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))

end DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
