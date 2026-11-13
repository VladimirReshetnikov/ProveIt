import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Source-only proposal: positive-parameter geometry for the auxiliary
bounds. The large-k inequality and Delta identity are explicit premises.
No graph theorem, elaboration or compilation is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AuxGeometryModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive Y and eta plus the explicit first-ordinate lower bound give
c>A and hence 1<c and 0<Delta<c³. No graph zero is assumed. -/
theorem geometry_of_large_k (X Y eta k Delta : V) (hY : 0<Y) (heta : 0<eta)
    (hk : 8*X*Y*Y+4≤k)
    (hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1) :
    let A := X*Y+Y+2
    let c := eta+Y*k
    A<c ∧ 1<c ∧ 0<Delta ∧ Delta<c*c*c := by
  let A : V := X*Y+Y+2
  let c : V := eta+Y*k
  have hY1 : 1≤Y := pos_iff_one_le.mp hY
  have hYsq : 1≤Y*Y := one_le_mul hY1 hY1
  have hXm : X≤X*Y*Y := by
    calc
      X=X*(1*1) := by ring
      _≤X*(Y*Y) := mul_le_mul_of_nonneg_left hYsq (Arithmetic.zero_le X)
      _=X*Y*Y := by ring
  have hm8 : X*Y*Y≤8*(X*Y*Y) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (by norm_num : (1:V)≤8) (Arithmetic.zero_le (X*Y*Y))
  have hXk : X+4≤k := calc
    X+4≤X*Y*Y+4 := add_le_add_right hXm 4
    _≤8*(X*Y*Y)+4 := add_le_add_right hm8 4
    _=8*X*Y*Y+4 := by ring
    _≤k := hk
  have hYk : Y*(X+4)≤Y*k := mul_le_mul_of_nonneg_left hXk (Arithmetic.zero_le Y)
  have h3Y : (3:V)≤3*Y := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hY1 (by norm_num : (0:V)≤3)
  have hAc : A<c := calc
    A=X*Y+Y+2 := rfl
    _<X*Y+Y+3 := add_lt_add_left (by norm_num : (2:V)<3) _
    _≤X*Y+Y+3*Y := add_le_add_left h3Y _
    _=Y*(X+4) := by ring
    _≤Y*k := hYk
    _<eta+Y*k := lt_add_of_pos_left _ heta
  have hA2 : (2:V)≤A := by
    dsimp only [A]
    exact le_add_of_nonneg_left (Arithmetic.zero_le (X*Y+Y))
  have hc : 1<c := lt_trans (lt_of_lt_of_le (by norm_num : (1:V)<2) hA2) hAc
  have hcpos : 0<c := lt_trans (by norm_num) hc
  have hAsq : A*A<c*c := calc
    A*A≤c*A := mul_le_mul_of_nonneg_right (le_of_lt hAc) (Arithmetic.zero_le A)
    _<c*c := mul_lt_mul_of_pos_left hAc hcpos
  have hDelta' : A*A=Delta+1 := by simpa only [A] using hDelta
  have hA1 : 1≤A := le_trans (by norm_num) hA2
  have hAsqgt : 1<A*A := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1:V)<2) hA2)
    (le_mul_of_one_le_right (Arithmetic.zero_le A) hA1)
  have hDeltaPos : 0<Delta := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h : A*A=1 := by simpa only [hz,zero_add] using hDelta'
    exact (ne_of_gt hAsqgt) h
  have hDeltaSq : Delta<c*c := calc
    Delta<Delta+1 := lt_add_one _
    _=A*A := hDelta'.symm
    _<c*c := hAsq
  have hc1 : 1≤c := le_of_lt hc
  have hc2cube : c*c≤c*c*c := le_mul_of_one_le_right (Arithmetic.zero_le (c*c)) hc1
  exact ⟨hAc,hc,hDeltaPos,lt_of_lt_of_le hDeltaSq hc2cube⟩

end DiophantineConsistency.AuxGeometryModelDraft

#print axioms DiophantineConsistency.AuxGeometryModelDraft.geometry_of_large_k
