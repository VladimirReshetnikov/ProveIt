import DiophantineConsistency.AdaptiveGap85BalanceContext

/-! A candidate second witness shift in arbitrary IΣ₁ models. The statements
keep all subtraction bounds explicit; no normalized representative is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveFirstRootFactor87Syntax ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
open AdaptiveDirectOrdinate86Context AdaptiveGap85Literal AdaptiveGap85BalanceContext
open AdaptiveGap85ShiftFirstInput AdaptiveGap85ShiftMainShift AdaptiveGap85ShiftAuxInput
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def shift (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V) : Fin 13 → V :=
  let b := v 0*(p 0:V)
  let q := 1+b
  let A := v 6+(p 1:V)*q
  let k := v 9+v 10
  ![v 0,v 1+b*t,v 2-q*b*t,v 3,v 4,v 5,v 6,v 7,
    v 8-q*t*(A+1)*(b*k+1),v 9,v 10,v 11,v 12]

theorem literal_preserved (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let k := v 9+v 10;
      q*t*(A+1)*(b*k+1)≤v 8) :
    Equivalent (pairEval (expressionAt85 (fun j => (p j:ℤ))) (shift p v t))
      (pairEval (expressionAt85 (fun j => (p j:ℤ))) v) := by
  let w := shift p v t
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let q3 : V := q*(q*q)
  let M : V := q3*b
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  let c : V := v 9+v 7*k
  have hJ : w 0=v 0 := rfl
  have hF : w 1=v 1+b*t := rfl
  have hX : w 6=v 6 := rfl
  have hY : w 7=v 7 := rfl
  have heta : w 9=v 9 := rfl
  have hzeta : w 10=v 10 := rfl
  have hf : w 3=v 3 := rfl
  have hT : w 5=v 5 := rfl
  have hg : w 12=v 12 := rfl
  have hC' : v 2=w 2+q*b*t := by
    dsimp [w,shift]
    exact (tsub_add_cancel_of_le hC).symm
  have hr' : v 8=w 8+q*t*(A+1)*(b*k+1) := by
    dsimp [w,shift]
    exact (tsub_add_cancel_of_le hr).symm
  have hbalance : w 1*q+w 2 = v 1*q+v 2 := by
    rw [hF,hC']
    ring
  have hfirst : Equivalent (pairEval (firstInput (fun j => (p j:ℤ))) w)
      (pairEval (firstInput (fun j => (p j:ℤ))) v) := by
    have hv := first_input_rep p v
    have hw := first_input_rep p w
    change SignedRep (firstInput (fun j => (p j:ℤ))) v
      (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) at hv
    have hw' : SignedRep (firstInput (fun j => (p j:ℤ))) w
      (M*(ell+k+w 8)+v 7*b+(M*k+q3)*(w 1*q),(M*k+q3)*(w 2*A)) := by
      simpa only [hJ,hX,hY,heta,hzeta,b,q,q3,M,k,ell,A] using hw
    have he : Equivalent
        (M*(ell+k+w 8)+v 7*b+(M*k+q3)*(w 1*q),(M*k+q3)*(w 2*A))
        (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) := by
      change M*(ell+k+w 8)+v 7*b+(M*k+q3)*(w 1*q)+(M*k+q3)*(v 2*A) =
        (M*k+q3)*(w 2*A)+(M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q))
      rw [hF,hC',hr']
      dsimp [M,q3]
      ring
    exact equivalent_trans hw' (equivalent_trans he (equivalent_symm hv))
  have hmain : Equivalent (pairEval (mainShift (fun j => (p j:ℤ))) w)
      (pairEval (mainShift (fun j => (p j:ℤ))) v) := by
    have hv := main_shift_rep p v
    have hw := main_shift_rep p w
    change SignedRep (mainShift (fun j => (p j:ℤ))) v
      (U*v 12+(v 6*v 7)*q+(q*q*H+P)+1,(v 1*q+v 2)*H+k) at hv
    have hw' : SignedRep (mainShift (fun j => (p j:ℤ))) w
      (U*v 12+(v 6*v 7)*q+(q*q*H+P)+1,(w 1*q+w 2)*H+k) := by
      simpa only [hJ,hX,hY,heta,hzeta,hg,b,q,U,H,P,k] using hw
    rw [hbalance] at hw'
    exact equivalent_trans hw' (equivalent_symm hv)
  have haux : Equivalent (pairEval (auxiliaryInput (fun j => (p j:ℤ))) w)
      (pairEval (auxiliaryInput (fun j => (p j:ℤ))) v) := by
    have hv := auxiliary_input_rep p v
    have hw := auxiliary_input_rep p w
    change SignedRep (auxiliaryInput (fun j => (p j:ℤ))) v
      (v 3*v 3*(v 5*c+(v 1*q+v 2)*H),v 3*v 3*(q*q*H+P)+c) at hv
    have hw' : SignedRep (auxiliaryInput (fun j => (p j:ℤ))) w
      (v 3*v 3*(v 5*c+(w 1*q+w 2)*H),v 3*v 3*(q*q*H+P)+c) := by
      simpa only [hJ,hf,hT,hY,heta,hzeta,b,q,H,P,k,c] using hw
    rw [hbalance] at hw'
    exact equivalent_trans hw' (equivalent_symm hv)
  have hcommon : ∀ i : Fin 13, ¬(i=1 ∨ i=2 ∨ i=5 ∨ i=8 ∨ i=12) → w i=v i := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact False.elim (hi (by decide))
  exact literal_equiv_of_balance_inputs p v w hcommon hfirst hmain haux

/-- The exact sum reduction is valid whenever the C decrement is available. -/
theorem shifted_gap_sum (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2) :
    let b := v 0*(p 0:V)
    shift p v t 1+shift p v t 2+b*b*t = v 1+v 2 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  change (v 1+b*t)+(v 2-q*b*t)+b*b*t = v 1+v 2
  calc
    _ = v 1+((v 2-q*b*t)+q*b*t) := by dsimp [q]; ring
    _ = v 1+v 2 := by rw [tsub_add_cancel_of_le hC]

/-- Strict subtraction bounds preserve every positive witness coordinate. -/
theorem shift_positive (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hv : ∀ i,0<v i)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t<v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let k := v 9+v 10;
      q*t*(A+1)*(b*k+1)<v 8) : ∀ i,0<shift p v t i := by
  intro i
  fin_cases i <;> dsimp [shift] <;> first
    | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 5 | exact hv 6
    | exact hv 7 | exact hv 9 | exact hv 10 | exact hv 11 | exact hv 12
    | exact add_pos_of_pos_of_nonneg (hv 1) (by simp)
    | exact tsub_pos_iff_lt.mpr hC
    | exact tsub_pos_iff_lt.mpr hr

/-- Under the explicit bounds, every positive zero yields a positive zero
with the displayed smaller gap sum. No representative existence is asserted. -/
theorem positive_zero_shift (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hv : ∀ i,0<v i)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t<v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let k := v 9+v 10;
      q*t*(A+1)*(b*k+1)<v 8)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    (∀ i,0<shift p v t i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) (shift p v t) ∧
      (let b := v 0*(p 0:V); shift p v t 1+shift p v t 2+b*b*t = v 1+v 2) := by
  refine ⟨shift_positive p v t hv hC hr, ?_, shifted_gap_sum p v t (le_of_lt hC)⟩
  exact (equivalent_zero_iff (literal_preserved p v t (le_of_lt hC) (le_of_lt hr))).2 hz
end DiophantineConsistency.AdaptiveGap85BalanceModel
