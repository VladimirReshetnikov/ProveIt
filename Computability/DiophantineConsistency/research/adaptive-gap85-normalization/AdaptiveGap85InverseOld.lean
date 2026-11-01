import DiophantineConsistency.AdaptiveGap85ShiftModel
import DiophantineConsistency.AdaptiveGap85Exists
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85InverseOld
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveDirectOrdinate86Context
open AdaptiveGap85Literal AdaptiveGap85Exists
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def inverse (p : Fin 4 → ℕ) (v : Fin 13 → V) : Fin 13 → V :=
  let b := v 0*(p 0:V)
  let q := 1+b
  let k := v 9+v 10
  let c := v 9+v 7*k
  let U := v 7*(q*q)
  let H := q*q-1
  let A := v 6+(p 1:V)*q
  let d := b*c*U
  let dr := d*A*k+c*U*A
  ![v 0,v 1,v 2-d,v 3,v 4,v 5+b*U*H,v 6,v 7,v 8-dr,
    v 9,v 10,v 11,v 12-b*c*H]

theorem shift_inverse (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); b*c*U≤v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); let A := v 6+(p 1:V)*q
      (b*c*U)*A*(v 9+v 10)+c*U*A≤v 8)
    (hg : let b := v 0*(p 0:V); let q := 1+b; let c := v 9+v 7*(v 9+v 10)
      b*c*(q*q-1)≤v 12) :
    AdaptiveGap85ShiftModel.shift p (inverse p v)=v := by
  funext i
  fin_cases i <;> simp [AdaptiveGap85ShiftModel.shift,inverse,
    tsub_add_cancel_of_le hC,tsub_add_cancel_of_le hg]
  simpa only [add_assoc] using (tsub_add_cancel_of_le hr)

/-- The explicit candidate also recovers any source tuple for an available
original forward shift. -/
theorem inverse_shift (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hT : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      b*U*(q*q-1)≤v 5) :
    inverse p (AdaptiveGap85ShiftModel.shift p v)=v := by
  funext i
  fin_cases i <;> simp [AdaptiveGap85ShiftModel.shift,inverse,tsub_add_cancel_of_le hT]
  simp [add_assoc]

theorem inverse_positive (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hv : ∀i,0<v i)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); b*c*U<v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); let A := v 6+(p 1:V)*q
      (b*c*U)*A*(v 9+v 10)+c*U*A<v 8)
    (hg : let b := v 0*(p 0:V); let q := 1+b; let c := v 9+v 7*(v 9+v 10)
      b*c*(q*q-1)<v 12) : ∀i,0 < inverse p v i := by
  intro i
  fin_cases i <;> dsimp [inverse] <;> first
    | exact hv 0 | exact hv 1 | exact hv 3 | exact hv 4 | exact hv 6
    | exact hv 7 | exact hv 9 | exact hv 10 | exact hv 11
    | exact tsub_pos_iff_lt.mpr hC | exact tsub_pos_iff_lt.mpr hr
    | exact tsub_pos_iff_lt.mpr hg
    | exact add_pos_of_pos_of_nonneg (hv 5) (by simp)

theorem inverse_positive_zero (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); b*c*U<v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); let A := v 6+(p 1:V)*q
      (b*c*U)*A*(v 9+v 10)+c*U*A<v 8)
    (hg : let b := v 0*(p 0:V); let q := 1+b; let c := v 9+v 7*(v 9+v 10)
      b*c*(q*q-1)<v 12) :
    (∀i,0 < inverse p v i) ∧ InternalZero (expressionAt85 (fun j => (p j:ℤ))) (inverse p v) := by
  have hp := inverse_positive p v hv hC hr hg
  have ht : let b := (inverse p v) 0*(p 0:V); let q := 1+b; let U := (inverse p v) 7*(q*q)
      b*U*(q*q-1)≤(inverse p v) 5 := by simp [inverse]
  have he := AdaptiveGap85ShiftModel.literal_preserved p (inverse p v) ht
  rw [shift_inverse p v (le_of_lt hC) (le_of_lt hr) (le_of_lt hg)] at he
  exact ⟨hp,(equivalent_zero_iff he).1 hz⟩

/-- Conditional inverse-old construction of a shifted natural 86-zero.
The explicit subtraction and reverse-gap bounds are not known for all zeros. -/
theorem inverse_old_zero_to_86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); b*c*U<v 2)
    (hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q)
      let c := v 9+v 7*(v 9+v 10); let A := v 6+(p 1:V)*q
      (b*c*U)*A*(v 9+v 10)+c*U*A<v 8)
    (hg : let b := v 0*(p 0:V); let q := 1+b; let c := v 9+v 7*(v 9+v 10)
      b*c*(q*q-1)<v 12)
    (hgap : (inverse p v) 1+(inverse p v) 2<1+(inverse p v) 0*(p 0:V)) :
    ∃ u : Fin 13 → V, InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) u := by
  obtain ⟨hw,hwz⟩ := inverse_positive_zero p v hv hz hC hr hg
  let u : Fin 13 → V := fun i => inverse p v i-1
  have hu : ∀ i, u i+1=inverse p v i := by
    intro i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hw i))
  have huz : InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) u :=
    AdaptiveDirectOrdinate86Witness.shifted_zero_of_positive hw hwz
  have hub : (u 1+1)+(u 2+1)<1+(u 0+1)*(p 0:V) := by
    rw [hu 1,hu 2,hu 0]
    exact hgap
  exact AdaptiveGap85Exists.new_natural_zero_to_old_of_bound p u hub huz
end DiophantineConsistency.AdaptiveGap85InverseOld
