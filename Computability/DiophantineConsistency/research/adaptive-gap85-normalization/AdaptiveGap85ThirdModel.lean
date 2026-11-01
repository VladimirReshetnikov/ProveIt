import DiophantineConsistency.AdaptiveGap85BalanceContext

/-! Third 85 shift in arbitrary IΣ₁ models. All required subtraction and
positivity bounds are explicit; this is not a normalization theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThirdModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveFirstRootFactor87Syntax ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
open AdaptiveDirectOrdinate86Context AdaptiveGap85Literal AdaptiveGap85BalanceContext
open AdaptiveGap85ShiftFirstInput AdaptiveGap85ShiftMainShift AdaptiveGap85ShiftAuxInput
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def shift (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V) : Fin 13 → V :=
  let b := v 0*(p 0:V)
  let q := 1+b
  let A := v 6+(p 1:V)*q
  let U := v 7*(q*q)
  let k := v 9+v 10
  let c := v 9+v 7*k
  let d := c*U*s
  let H := q*q-1
  ![v 0,v 1-A*d,v 2+(b*A-1)*d,v 3,v 4,
    v 5+H*(A+1)*U*s,v 6,v 7,
    v 8+A*(A+1)*(b*k+1)*d,v 9,v 10,v 11,
    v 12-H*(A+1)*c*s]

theorem literal_preserved (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hBA : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; 1≤b*A)
    (hF : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); A*(c*U*s)≤v 1)
    (hg : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let c := v 9+v 7*(v 9+v 10);
      (q*q-1)*(A+1)*c*s≤v 12) :
    Equivalent (pairEval (expressionAt85 (fun j => (p j:ℤ))) (shift p v s))
      (pairEval (expressionAt85 (fun j => (p j:ℤ))) v) := by
  let w := shift p v s
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
  let d : V := c*U*s
  let B : V := b*A-1
  let E : V := (A+1)*d
  let I : V := H*(A+1)*U*s
  let G : V := H*(A+1)*c*s
  let R : V := A*(A+1)*(b*k+1)*d
  have hbA : B+1=b*A := tsub_add_cancel_of_le hBA
  have hBq : B+q=b*(A+1) := by
    calc
      _ = (B+1)+b := by dsimp [q]; ring
      _ = b*A+b := by rw [hbA]
      _ = _ := by ring
  have hBAq : B+(A+1)=A*q := by
    calc
      _ = (B+1)+A := by ring
      _ = b*A+A := by rw [hbA]
      _ = _ := by dsimp [q]; ring
  have hJ : w 0=v 0 := rfl
  have hX : w 6=v 6 := rfl
  have hY : w 7=v 7 := rfl
  have heta : w 9=v 9 := rfl
  have hzeta : w 10=v 10 := rfl
  have hf : w 3=v 3 := rfl
  have hwC : w 2=v 2+B*d := rfl
  have hwT : w 5=v 5+I := rfl
  have hwr : w 8=v 8+R := rfl
  have hvF : v 1=w 1+A*d := by
    dsimp [w,shift]
    exact (tsub_add_cancel_of_le hF).symm
  have hvg : v 12=w 12+G := by
    dsimp [w,shift]
    exact (tsub_add_cancel_of_le hg).symm
  have hrank : w 1*q+w 2+E=v 1*q+v 2 := by
    rw [hwC]
    calc
      _ = w 1*q+v 2+(B+(A+1))*d := by dsimp [E]; ring
      _ = w 1*q+v 2+(A*q)*d := by rw [hBAq]
      _ = (w 1+A*d)*q+v 2 := by ring
      _ = _ := by rw [←hvF]
  have hfirst : Equivalent (pairEval (firstInput (fun j => (p j:ℤ))) w)
      (pairEval (firstInput (fun j => (p j:ℤ))) v) := by
    have hv := first_input_rep p v
    have hw := first_input_rep p w
    change SignedRep (firstInput (fun j => (p j:ℤ))) v
      (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) at hv
    have hw' : SignedRep (firstInput (fun j => (p j:ℤ))) w
      (M*(ell+k+w 8)+v 7*b+(M*k+q3)*(w 1*q),(M*k+q3)*(w 2*A)) := by
      simpa only [hJ,hX,hY,heta,hzeta,b,q,q3,M,k,ell,A] using hw
    have hprod : M*R = (M*k+q3)*A*d*(B+q) := by
      rw [hBq]
      dsimp [M,q3,R]
      ring
    have he : Equivalent
        (M*(ell+k+w 8)+v 7*b+(M*k+q3)*(w 1*q),(M*k+q3)*(w 2*A))
        (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) := by
      change M*(ell+k+w 8)+v 7*b+(M*k+q3)*(w 1*q)+(M*k+q3)*(v 2*A) =
        (M*k+q3)*(w 2*A)+(M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q))
      rw [hwr,hwC,hvF]
      calc
        _ = (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(w 1*q)+(M*k+q3)*(v 2*A))+M*R := by ring
        _ = (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(w 1*q)+(M*k+q3)*(v 2*A))+
            (M*k+q3)*A*d*(B+q) := by rw [hprod]
        _ = _ := by ring
    exact equivalent_trans hw' (equivalent_trans he (equivalent_symm hv))
  have hmain : Equivalent (pairEval (mainShift (fun j => (p j:ℤ))) w)
      (pairEval (mainShift (fun j => (p j:ℤ))) v) := by
    have hv := main_shift_rep p v
    have hw := main_shift_rep p w
    change SignedRep (mainShift (fun j => (p j:ℤ))) v
      (U*v 12+(v 6*v 7)*q+(q*q*H+P)+1,(v 1*q+v 2)*H+k) at hv
    have hw' : SignedRep (mainShift (fun j => (p j:ℤ))) w
      (U*w 12+(v 6*v 7)*q+(q*q*H+P)+1,(w 1*q+w 2)*H+k) := by
      simpa only [hJ,hX,hY,heta,hzeta,b,q,U,H,P,k] using hw
    have he : Equivalent
      (U*w 12+(v 6*v 7)*q+(q*q*H+P)+1,(w 1*q+w 2)*H+k)
      (U*v 12+(v 6*v 7)*q+(q*q*H+P)+1,(v 1*q+v 2)*H+k) := by
      change U*w 12+(v 6*v 7)*q+(q*q*H+P)+1+((v 1*q+v 2)*H+k) =
        ((w 1*q+w 2)*H+k)+(U*v 12+(v 6*v 7)*q+(q*q*H+P)+1)
      rw [←hrank,hvg]
      dsimp [E,G,d,U]
      ring
    exact equivalent_trans hw' (equivalent_trans he (equivalent_symm hv))
  have haux : Equivalent (pairEval (auxiliaryInput (fun j => (p j:ℤ))) w)
      (pairEval (auxiliaryInput (fun j => (p j:ℤ))) v) := by
    have hv := auxiliary_input_rep p v
    have hw := auxiliary_input_rep p w
    change SignedRep (auxiliaryInput (fun j => (p j:ℤ))) v
      (v 3*v 3*(v 5*c+(v 1*q+v 2)*H),v 3*v 3*(q*q*H+P)+c) at hv
    have hw' : SignedRep (auxiliaryInput (fun j => (p j:ℤ))) w
      (v 3*v 3*(w 5*c+(w 1*q+w 2)*H),v 3*v 3*(q*q*H+P)+c) := by
      simpa only [hJ,hf,hY,heta,hzeta,b,q,H,P,k,c] using hw
    have he : Equivalent
      (v 3*v 3*(w 5*c+(w 1*q+w 2)*H),v 3*v 3*(q*q*H+P)+c)
      (v 3*v 3*(v 5*c+(v 1*q+v 2)*H),v 3*v 3*(q*q*H+P)+c) := by
      change v 3*v 3*(w 5*c+(w 1*q+w 2)*H)+(v 3*v 3*(q*q*H+P)+c) =
        (v 3*v 3*(q*q*H+P)+c)+v 3*v 3*(v 5*c+(v 1*q+v 2)*H)
      rw [←hrank,hwT]
      dsimp [I,E,d,U]
      ring
    exact equivalent_trans hw' (equivalent_trans he (equivalent_symm hv))
  have hcommon : ∀ i : Fin 13, ¬(i=1 ∨ i=2 ∨ i=5 ∨ i=8 ∨ i=12) → w i=v i := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact False.elim (hi (by decide))
  exact literal_equiv_of_balance_inputs p v w hcommon hfirst hmain haux

/-- Strict F and gamma subtraction bounds keep every coordinate positive. -/
theorem shift_positive (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hv : ∀ i,0<v i)
    (hF : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); A*(c*U*s)<v 1)
    (hg : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let c := v 9+v 7*(v 9+v 10);
      (q*q-1)*(A+1)*c*s<v 12) : ∀ i,0<shift p v s i := by
  intro i
  fin_cases i <;> dsimp [shift] <;> first
    | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 6 | exact hv 7
    | exact hv 9 | exact hv 10 | exact hv 11
    | exact add_pos_of_pos_of_nonneg (hv 2) (by simp)
    | exact add_pos_of_pos_of_nonneg (hv 5) (by simp)
    | exact add_pos_of_pos_of_nonneg (hv 8) (by simp)
    | exact tsub_pos_iff_lt.mpr hF
    | exact tsub_pos_iff_lt.mpr hg

/-- Under the displayed bounds the third shift preserves a positive zero.
No claim is made that the bounds hold for an arbitrary positive zero. -/
theorem positive_zero_shift (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hv : ∀ i,0<v i)
    (hBA : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; 1≤b*A)
    (hF : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); A*(c*U*s)<v 1)
    (hg : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let c := v 9+v 7*(v 9+v 10);
      (q*q-1)*(A+1)*c*s<v 12)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    (∀ i,0<shift p v s i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) (shift p v s) := by
  refine ⟨shift_positive p v s hv hF hg, ?_⟩
  exact (equivalent_zero_iff (literal_preserved p v s hBA (le_of_lt hF) (le_of_lt hg))).2 hz

/-- The exact amount by which the F coordinate is decreased. -/
theorem shifted_F_sum (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hF : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); A*(c*U*s)≤v 1) :
    let b := v 0*(p 0:V); let q := 1+b;
    let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
    let c := v 9+v 7*(v 9+v 10);
    shift p v s 1+A*(c*U*s)=v 1 := by
  dsimp [shift]
  exact tsub_add_cancel_of_le hF
end DiophantineConsistency.AdaptiveGap85ThirdModel
