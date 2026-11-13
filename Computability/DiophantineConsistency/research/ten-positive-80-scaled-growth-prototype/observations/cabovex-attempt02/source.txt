import Direct80GraphIndex

/-! Recover c>X directly from the graph's first and main Pell ordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80CAboveX
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open TenPositive80Graph TenPositive80Factors TenPositive80Pell Direct80GraphIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_c_above_x (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) : X p v<c p v := by
  obtain ⟨tau,f,n,I,_,_,_,_,_,_,_,hny,_⟩ := first_and_doubled p v hb hv hz
  have hn2 := first_index_ge_two p v n hb hv hz hny
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hy
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hS : 1≤mu p v*Y p v := pos_iff_one_le.mp (mul_pos hmu hy)
  have hP : 0<P := mul_pos hx (mul_pos (mul_pos hmu hy) (mul_pos hmu hy))
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  have hy1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
  have hx1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
  have hy2 : ycoord 2 B=2*(B+2) := by
    calc
      ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
      _=2*(B+2) := by rw [hx1,hy1]; ring
  have hklower : 8*P+4≤k v := calc
    8*P+4=2*ycoord 2 B := by rw [hy2,hB]; ring
    _≤2*ycoord n B := mul_le_mul_of_nonneg_left ((ordinate_strictMono B).monotone hn2) (by simp)
    _=k v := hny
  have hXP : X p v≤P := by
    change X p v≤X p v*((mu p v*Y p v)*(mu p v*Y p v))
    exact le_mul_of_one_le_right (by simp) (one_le_mul hS hS)
  have hPk : P<k v := calc
    P≤8*P := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:V)≤8 by norm_num) (show (0:V)≤P by simp)
    _<8*P+4 := lt_add_of_pos_right _ (by norm_num)
    _≤k v := hklower
  have hkc : k v≤c p v := by
    change k v≤k v*Y p v+v 8
    exact le_trans (le_mul_of_one_le_right (by simp) hY1) (by simp)
  exact lt_of_lt_of_le (lt_of_le_of_lt hXP hPk) hkc

#print axioms Direct80CAboveX.graph_c_above_x
end Direct80CAboveX
