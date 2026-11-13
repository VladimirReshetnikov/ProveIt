import PellRecovery
import Direct80Consequences

/-! Noncircular odd-ordinate recovery for actual positive 80-graph zeros. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80Fold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open TenPositive80Graph TenPositive80Factors TenPositive80Consequences TenPositivePellRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_odd_ordinate (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r j I : V, 0<r ∧ r<j ∧ r%2=1 ∧ 0<j ∧ 0<I ∧
      c p v=ycoord r (A p v-1) ∧
      xcoord j (A p v-1)=1+2*(delta p v*U p v*U p v*E p v) ∧
      ycoord j (A p v-1)=I ∧ c p v*c p v∣I := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let A0 : V := A p v
  let C : V := c p v
  let F : V := 1+2*(D*U0*U0*E0)
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hmuY : 1≤mu p v*Y p v := pos_iff_one_le.mp (mul_pos hmu hY)
  have hX2 : 2≤X p v+1 := by
    simpa only [show (2:V)=1+1 by ring, add_comm] using _root_.add_le_add_right (pos_iff_one_le.mp hX) (1:V)
  have hA2 : 2≤A0 := by
    calc
      2≤X p v+1 := hX2
      _≤(mu p v*Y p v)*(X p v+1) := le_mul_of_one_le_left (by simp) hmuY
      _=A0 := rfl
  have hD4 : 4≤D := by
    calc
      4=(2:V)*2 := by ring
      _≤A0*2 := mul_le_mul_of_nonneg_right hA2 (by simp)
      _≤A0*(A0+2) := mul_le_mul_of_nonneg_left (by simp) (by simp)
      _=D := rfl
  have hk2 : 2≤k v := by
    simpa only [k,show (2:V)=1+1 by ring] using
      _root_.add_le_add (pos_iff_one_le.mp (hv 8)) (pos_iff_one_le.mp (hv 9))
  have hkY : k v≤k v*Y p v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v)
  have hC2 : 2<C := lt_of_le_of_lt (le_trans hk2 hkY) (by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ (hv 8))
  have hC : 0<C := lt_trans (by simp : (0:V)<2) hC2
  obtain ⟨I,j,h,hI,hj,hCI,hdiv,hjx,hjy,hcong⟩ := signed_coordinate p v hb hv hz
  have hCsq : C*C≤I := Arithmetic.le_of_dvd hI hdiv
  have hCstrict : C<C*C := by
    have h1 : 1<C := lt_trans (by simp : (1:V)<2) hC2
    simpa only [mul_one] using mul_lt_mul_of_pos_left h1 hC
  have hCIstrict : C<I := lt_of_lt_of_le hCstrict hCsq
  have hApos : 0<A0 := lt_of_lt_of_le (by simp : (0:V)<2) hA2
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hdelta : ArithmeticPellRecurrence.delta (A0-1)=D := by
    unfold ArithmeticPellRecurrence.delta
    have h3 : A0-1+3=(A0-1+1)+2 := by ring
    rw [h3,hA1]
    rfl
  have hnorm : F*F=1+D*I*I := by
    have h := norm j (A0-1)
    rw [hdelta,hjx,hjy] at h
    exact h
  have hFsize : 2*I<F := by
    by_contra hn
    have hle : F≤2*I := le_of_not_gt hn
    have hsq : F*F≤(2*I)*(2*I) := mul_self_le_mul_self (by simp) hle
    have hmul : 4*I*I≤D*I*I := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hD4 (by simp)) (by simp)
    have hlt : (2*I)*(2*I)<F*F := by
      calc
        (2*I)*(2*I)=4*I*I := by ring
        _≤D*I*I := hmul
        _<1+D*I*I := by simp
        _=F*F := hnorm.symm
    exact (not_le_of_gt hlt) hsq
  have hsodd : (2*h+1)%2=1 := by rw [mod_add (by simp : (0:V)<2),mod_mul_self_right]; simp
  obtain ⟨r,hr,hrj,hrodd,heq⟩ := recover_odd_ordinate j (2*h+1) (A0-1) C hj hsodd hC
    (by rwa [hjy]) (by rwa [hjy,hjx]) (by rwa [hjx])
  exact ⟨r,j,I,hr,hrj,hrodd,hj,hI,heq,hjx,hjy,hdiv⟩

#print axioms TenPositive80Fold.graph_odd_ordinate
end TenPositive80Fold
