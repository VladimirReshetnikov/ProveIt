import DiophantineConsistency.Compact44.DirectMainProjection
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! A square lower bound from the third first-Pell ordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainPellGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_bound (Q n k : V) (hQ : 0<Q) (hn : 3≤n)
    (hk : 2*ycoord n (2*(Q-1)+1)=k) : Q*Q≤k := by
  let B : V := 2*(Q-1)+1
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  have hQB : Q≤B := by
    apply (add_le_add_iff_right (1:V)).mp
    calc
      Q+1≤Q+Q := _root_.add_le_add (le_refl Q) (pos_iff_one_le.mp hQ)
      _=B+1 := by rw [hB]; ring
  have hy1 : ycoord (1:V) B=1 := by simpa using y_succ (0:V) B
  have hy2 : 2*B+3<ycoord (2:V) B := by
    have h := y_lower B (1:V)
    simpa only [hy1,mul_one,show (1:V)+1=2 by ring] using h
  have hy3 : (2*B+3)*ycoord (2:V) B<ycoord (3:V) B := by
    have h := y_lower B (2:V)
    simpa only [show (2:V)+1=3 by ring] using h
  have hBcoef : B≤2*B+3 := by
    calc
      B≤B+(B+3) := by simp
      _=2*B+3 := by ring
  have hBy2 : B≤ycoord (2:V) B := le_trans hBcoef (le_of_lt hy2)
  have hBsq : B*B≤(2*B+3)*ycoord (2:V) B :=
    mul_le_mul hBcoef hBy2 (by simp) (by simp)
  have hQsq : Q*Q≤B*B := mul_le_mul hQB hQB (by simp) (by simp)
  have hyn : ycoord (3:V) B≤ycoord n B := (y_strictMono B).monotone hn
  calc
    Q*Q≤B*B := hQsq
    _≤(2*B+3)*ycoord (2:V) B := hBsq
    _≤ycoord (3:V) B := le_of_lt hy3
    _≤ycoord n B := hyn
    _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
    _=k := hk

#print axioms DirectMainPellGrowth.square_bound
end DirectMainPellGrowth
