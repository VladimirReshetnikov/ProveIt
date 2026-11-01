import DiophantineConsistency.AdaptiveGap85ShiftContextEquiv

/-! Full literal shift in arbitrary IΣ₁ models, with explicit T bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveFirstRootFactor87Syntax ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 AdaptiveDirectOrdinate86Context
open AdaptiveGap85Literal AdaptiveGap85ShiftContextEquiv AdaptiveGap85ShiftFirstInput
open AdaptiveGap85ShiftMainShift AdaptiveGap85ShiftAuxInput
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def shift (p : Fin 4 → ℕ) (v : Fin 13 → V) : Fin 13 → V :=
  let b := v 0*(p 0:V)
  let q := 1+b
  let k := v 9+v 10
  let c := v 9+v 7*k
  let U := v 7*(q*q)
  let H := q*q-1
  let A := v 6+(p 1:V)*q
  let d := b*c*U
  ![v 0,v 1,v 2+d,v 3,v 4,v 5-b*U*H,v 6,v 7,v 8+d*A*k+c*U*A,
    v 9,v 10,v 11,v 12+b*c*H]

/-- The exact internal literal has equivalent signed evaluations under the
    coordinate shift whenever T permits its subtraction. -/
theorem literal_preserved (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hT : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      b*U*(q*q-1)≤v 5) :
    Equivalent (pairEval (expressionAt85 (fun j => (p j:ℤ))) (shift p v))
      (pairEval (expressionAt85 (fun j => (p j:ℤ))) v) := by
  let w := shift p v
  have hJ : w 0=v 0 := rfl
  have hF : w 1=v 1 := rfl
  have hf : w 3=v 3 := rfl
  have hX : w 6=v 6 := rfl
  have hY : w 7=v 7 := rfl
  have heta : w 9=v 9 := rfl
  have hzeta : w 10=v 10 := rfl
  have hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); w 2=v 2+b*c*U := rfl
  have hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      let k := v 9+v 10; let c := v 9+v 7*k; let A := v 6+(p 1:V)*q;
      w 8=v 8+b*c*U*A*k+c*U*A := rfl
  have hg : let b := v 0*(p 0:V); let q := 1+b;
      let c := v 9+v 7*(v 9+v 10); w 12=v 12+b*c*(q*q-1) := rfl
  have hT' : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      v 5=w 5+b*U*(q*q-1) := by
    dsimp [w,shift]
    exact (tsub_add_cancel_of_le hT).symm
  have hcommon : ∀ i : Fin 13, ¬(i=2 ∨ i=5 ∨ i=8 ∨ i=12) → w i=v i := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact False.elim (hi (by decide))
  exact literal_equiv_of_inputs p v w hcommon
    (first_input_preserved p v w hJ hF hX hY heta hzeta hC hr)
    (main_shift_preserved p v w hJ hF hX hY heta hzeta hC hg)
    (auxiliary_input_preserved p v w hJ hF hf hY heta hzeta hC hT')

/-- A sufficiently large positive zero shifts to a positive zero that fails
    the pointwise gap bound. This does not assert existence of any zero. -/
theorem shifted_zero_breaks_gap (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ i,0<v i)
    (hT : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      b*U*(q*q-1)<v 5)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    (∀ i,0<shift p v i) ∧ InternalZero (expressionAt85 (fun j => (p j:ℤ))) (shift p v) ∧
      ¬(shift p v 1+shift p v 2<1+shift p v 0*(p 0:V)) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let A : V := v 6+(p 1:V)*q
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := by dsimp [q]; exact add_pos_of_pos_of_nonneg (by norm_num) (by simp)
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) hk)
  have hU : 0<U := mul_pos (hv 7) (mul_pos hq hq)
  have hc1 : (1:V)≤c := pos_iff_one_le.mp hc
  have hU1 : (1:V)≤U := pos_iff_one_le.mp hU
  have hdelta : b≤b*c*U := le_trans (le_mul_of_one_le_right (by simp) hc1)
    (le_mul_of_one_le_right (by simp) hU1)
  have h8 : 0<v 8+b*c*U*A*k+c*U*A :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (hv 8) (by simp)) (by simp)
  dsimp [b,q,k,c,U,H,A] at h8
  have hp : ∀ i,0<shift p v i := by
    intro i
    fin_cases i <;> dsimp [shift] <;> first
      | exact hv 0 | exact hv 1 | exact hv 3 | exact hv 4 | exact hv 6
      | exact hv 7 | exact hv 9 | exact hv 10 | exact hv 11
      | exact tsub_pos_iff_lt.mpr hT
      | apply add_pos_of_pos_of_nonneg (hv 2); simp
      | exact h8
      | apply add_pos_of_pos_of_nonneg (hv 12); simp
  have he := literal_preserved p v (le_of_lt hT)
  have hz' : InternalZero (expressionAt85 (fun j => (p j:ℤ))) (shift p v) := by
    apply (equivalent_zero_iff he).2
    exact hz
  refine ⟨hp,hz',?_⟩
  change ¬(v 1+(v 2+b*c*U)<1+b)
  apply not_lt_of_ge
  calc
    1+b≤v 1+b*c*U := add_le_add (pos_iff_one_le.mp (hv 1)) hdelta
    _≤v 1+(v 2+b*c*U) := add_le_add (le_refl _) (le_add_of_nonneg_left (Arithmetic.zero_le (v 2)))
end DiophantineConsistency.AdaptiveGap85ShiftModel
