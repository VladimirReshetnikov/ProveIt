import DirectBFSCoefficientMass
import DiophantineConsistency.CompactIndexedMass
import DiophantineConsistency.CompactSelectorMassBridge

/-! The direct-BFS aligned family has carry slack in every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSModelMass
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency CompactGenericAlignedMass
attribute [local irreducible] DirectBFSSymbolicKernel.rows

def selectors (i : Fin 943) : ℕ := CompactCoefficientMass.selector (DirectBFSSymbolicKernel.row i)
def copies (j : Fin 41) : ℕ := 2^(10+j.val)

theorem rows_ofFn : List.ofFn DirectBFSSymbolicKernel.row = DirectBFSSymbolicKernel.rows := by
  unfold DirectBFSSymbolicKernel.row
  exact CompactSelectorMassBridge.ofFn_get_cast DirectBFSSymbolicKernel.rows DirectBFSSymbolicKernel.rows_length

theorem selectors_mass : (∑ i, selectors i) = DirectBFSCoefficientMass.selectorMass := by
  unfold selectors
  rw [←Fin.sum_ofFn]
  rw [List.ofFn_comp',rows_ofFn]
  rfl

theorem copies_mass : (∑ j, copies j) = DirectBFSCoefficientMass.copyMass := by
  rw [DirectBFSCoefficientMass.copy_mass_exact]
  decide

theorem natural_mass : (∑ x : Aligned (Fin 943) (Fin 41), alignedCoeff selectors copies x)+1 =
    DirectBFSCoefficientMass.stencilMass := by
  rw [sum_identity,selectors_mass,copies_mass]
  unfold DirectBFSCoefficientMass.stencilMass DirectBFSCoefficientMass.coefficientMass
  rfl

private theorem cast_sum_generic {V ι : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s, f i : ℕ) : V) = ∑ i ∈ s, (f i : V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem stencil_below_half : 3*(DirectBFSCoefficientMass.stencilMass:V)+1<Exp.exp 66 := by
  have hm : 3*(DirectBFSCoefficientMass.stencilMass:V)+1<((2^66:ℕ):V) := by
    exact_mod_cast DirectBFSCoefficientMass.triple_stencil_below_half
  have he : ((2^66:ℕ):V)=Exp.exp (66:V) := by
    simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 66).symm
  rwa [he] at hm

theorem stencil_mass_b1 :
    3*(DirectBFSCoefficientMass.stencilMass:V)+(Exp.exp 67-1)+1 ≤
      ((1:V)+1)*(Exp.exp 67-1) := by
  have hn : 3*DirectBFSCoefficientMass.stencilMass+2≤2^67 := by
    rw [DirectBFSCoefficientMass.stencil_mass_exact]
    decide
  have hm : 3*(DirectBFSCoefficientMass.stencilMass:V)+2≤((2^67:ℕ):V) := by exact_mod_cast hn
  have he : ((2^67:ℕ):V)=Exp.exp (67:V) := by
    simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 67).symm
  rw [he] at hm
  have hr : Exp.exp (67:V)-1+1=Exp.exp 67 := tsub_add_cancel_of_le (one_le_exp _)
  have hsmall : 3*(DirectBFSCoefficientMass.stencilMass:V)+1≤Exp.exp 67-1 := by
    apply (add_le_add_iff_right 1).mp
    calc
      (3*(DirectBFSCoefficientMass.stencilMass:V)+1)+1=3*(DirectBFSCoefficientMass.stencilMass:V)+2 := by ring
      _≤Exp.exp 67 := hm
      _=(Exp.exp 67-1)+1 := hr.symm
  calc
    3*(DirectBFSCoefficientMass.stencilMass:V)+(Exp.exp 67-1)+1 =
        (3*(DirectBFSCoefficientMass.stencilMass:V)+1)+(Exp.exp 67-1) := by ring
    _≤(Exp.exp 67-1)+(Exp.exp 67-1) := add_le_add_left hsmall _
    _=((1:V)+1)*(Exp.exp 67-1) := by ring

theorem family_mass_b1 :
    ((∑ x : Aligned (Fin 943) (Fin 41), ((alignedCoeff selectors copies x : ℕ):V)*3)+
      (Exp.exp 67-1))+1≤((1:V)+1)*(Exp.exp 67-1) := by
  have hm := congrArg (fun n : ℕ => (n:V)) natural_mass
  simp only [Nat.cast_add,Nat.cast_one,cast_sum_generic] at hm
  have hcoeff : (∑ x : Aligned (Fin 943) (Fin 41), ((alignedCoeff selectors copies x : ℕ):V))≤
      (DirectBFSCoefficientMass.stencilMass:V) := by rw [←hm]; exact le_add_of_nonneg_right (by simp)
  have h3 : (∑ x : Aligned (Fin 943) (Fin 41), ((alignedCoeff selectors copies x : ℕ):V)*3) ≤
      3*(DirectBFSCoefficientMass.stencilMass:V) := by
    rw [←Finset.sum_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcoeff (by simp : (0:V)≤3)
  exact le_trans (add_le_add_left (add_le_add_left h3 _) _) stencil_mass_b1

#print axioms DirectBFSModelMass.selectors_mass
#print axioms DirectBFSModelMass.natural_mass
#print axioms DirectBFSModelMass.stencil_below_half
#print axioms DirectBFSModelMass.family_mass_b1
end DirectBFSModelMass
