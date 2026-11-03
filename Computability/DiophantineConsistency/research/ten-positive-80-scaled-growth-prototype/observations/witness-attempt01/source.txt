import Direct80ScaledGrowthMinus
import Direct80Pell

/-! Apply the corrected growth bound to an explicitly aligned witness pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80GrowthWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
open TenPositive80Graph TenPositive80Factors TenPositive80Pell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem growth_of_witnesses (p : Fin 4 → ℕ) (v : Fin 10 → V) (n m : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hX : 16≤X p v)
    (hn3 : 3≤n) (hmrel : m+1=2*n)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord m (A p v-1)) : Exp.exp m<Y p v := by
  let r : V := n-1
  have hn1 : 1≤n := le_trans (by norm_num : (1:V)≤3) hn3
  have hrplus : r+1=n := tsub_add_cancel_of_le hn1
  have hr2 : 2≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrplus]
    simpa only [show (2:V)+1=3 by ring] using hn3
  have hmform : m=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      m+1=2*n := hmrel
      _=2*(r+1) := by rw [hrplus]
      _=(2*r+1)+1 := by ring
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hS : 1≤mu p v*Y p v := pos_iff_one_le.mp (mul_pos hmu hy)
  have hkc : c p v=k v*Y p v+v 8 := by rfl
  have hkez : k v=v 8+v 9 := by rfl
  have hc' : c p v=ycoord (2*r+1) ((mu p v*Y p v)*(X p v+1)-1) := by
    simpa only [hmform,A] using hc
  have hp : firstParam p v=X p v*(mu p v*Y p v)*(mu p v*Y p v) := by
    dsimp [firstParam]; ring
  have hk' : k v=2*ycoord (r+1) (2*(X p v*(mu p v*Y p v)*(mu p v*Y p v)-1)+1) := by
    rw [hrplus,←hp]
    exact hny.symm
  have hg := Direct80ScaledGrowthMinus.power_bound_scaled_minus (X p v) (Y p v)
    (mu p v*Y p v) r (k v) (c p v) (v 8) (v 9) hX hS hr2 hkc hkez (hv 9) hc' hk'
  simpa only [hmform] using hg

#print axioms Direct80GrowthWitness.growth_of_witnesses
end Direct80GrowthWitness
