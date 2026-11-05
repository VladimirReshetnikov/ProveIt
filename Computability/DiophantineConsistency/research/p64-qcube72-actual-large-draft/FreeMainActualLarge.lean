import FreeMainGraphMainRoot
import FreeMainIndexLower
import DiophantineConsistency.ArithmeticPellResidueAux

/-! Unchecked draft: actual 72-zero main index and large-c bound at q≥33. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainActualLarge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellResidueAux
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_index_large (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (hq : 33≤(p 0:V)*v 0+1) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let U := Y*Y
    let X := v 8*q
    let a := X*Y+Y
    let H := 4*a+3
    let c := (v 10+v 11)*Y+v 10
    ∃ g m : V, g*g=1+delta a*c*c ∧
      U*g=U*(X+a*c)+H*v 13 ∧
      xcoord m a=g ∧ ycoord m a=c ∧ 6≤m ∧ (a+2)*delta a*delta a<c := by
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let U : V := Y*Y
  let X : V := v 8*q
  let a : V := X*Y+Y
  let H : V := 4*a+3
  let c : V := (v 10+v 11)*Y+v 10
  obtain ⟨g,m,hg,hcarrier,hx,hy⟩ := FreeMainGraphMainRoot.main_index p v hv hz
  change g*g=1+delta a*c*c at hg
  change U*g=U*(X+a*c)+H*v 13 at hcarrier
  change xcoord m a=g at hx
  change ycoord m a=c at hy
  have hX : q≤X := by
    dsimp [X]
    exact le_mul_of_one_le_left (Arithmetic.zero_le q) (pos_iff_one_le.mp (hv 8))
  have hY : (3:V)≤Y := by
    have hq1 : (1:V)≤q := le_trans (by norm_num) hq
    calc
      (3:V) ≤ q := le_trans (by norm_num) hq
      _ ≤ q*q*q := by
        simpa only [mul_assoc] using le_mul_of_one_le_right (Arithmetic.zero_le q)
          (one_le_mul_of_one_le_of_one_le hq1 hq1)
      _ ≤ q*q*q*v 7 := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 7))
      _ = Y := rfl
  have hm : 6≤m := FreeMainIndexLower.six_le_index q X Y U a H g c (v 13) m
    hq hX hY rfl rfl rfl hx hy hcarrier
  have hbig : (a+2)*delta a*delta a<c := by
    rw [←hy]
    exact large_of_six a m hm
  exact ⟨g,m,hg,hcarrier,hx,hy,hm,hbig⟩

#print axioms FreeMainActualLarge.main_index_large
end FreeMainActualLarge
