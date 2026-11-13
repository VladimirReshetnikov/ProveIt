import Direct80ScaledGrowthMinus
import Direct80Pell
import Direct80MainNorm

/-! Apply the corrected growth bound to 80 graph zeros under index alignment. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80GraphGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open TenPositive80Graph TenPositive80Factors TenPositive80Pell TenPositive80MainNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_growth_of_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (hX : 16≤X p v)
    (halign : ∀ n m : V, 0<n → n≤k v → 0<m →
      2*ycoord n (2*(firstParam p v-1)+1)=k v →
      c p v=ycoord m (A p v-1) → 3≤n ∧ m+1=2*n) :
    ∃ n m : V, 3≤n ∧ 0<m ∧ m+1=2*n ∧ Exp.exp m<Y p v := by
  obtain ⟨tau,f,n,I,_,_,hn,hnk,_,_,_,hny,_⟩ := first_and_doubled p v hb hv hz
  obtain ⟨m,j,d,I',hm,_,_,_,_,_,_,hc,_,_⟩ := graph_main_norm p v hb hv hz
  obtain ⟨hn3,hmrel⟩ := halign n m hn hnk hm hny hc
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
  refine ⟨n,m,hn3,hm,hmrel,?_⟩
  simpa only [hmform] using hg

#print axioms Direct80GraphGrowth.graph_growth_of_alignment
end Direct80GraphGrowth
