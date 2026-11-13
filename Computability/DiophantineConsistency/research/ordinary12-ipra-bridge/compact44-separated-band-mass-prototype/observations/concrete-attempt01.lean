import DiophantineConsistency.CompactSelectorMassBridge
import DiophantineConsistency.CompactGenericAlignedMass
import DiophantineConsistency.CompactModelStencilSlack
set_option autoImplicit false
set_option Elab.async false
noncomputable section
attribute [local irreducible] Compact943Data.rows
namespace CompactConcreteAlignedMass
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactGenericAlignedMass CompactSelectorMassBridge
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev Aligned := CompactGenericAlignedMass.Aligned (Fin 943) (Fin 41)
def selectors (i : Fin 943) : ℕ := CompactCoefficientMass.selector (Compact943Data.row i)
def copies (j : Fin 41) : ℕ := 2^(10+j.val)
def coeffNat : Aligned → ℕ := alignedCoeff selectors copies
def coeff (i : Aligned) : V := (coeffNat i:V)

theorem aligned_mass_nat : (∑ i : Aligned, coeffNat i)+1 =
    CompactCoefficientMass.stencilMass := by
  have h := CompactGenericAlignedMass.sum_identity selectors copies
  change (∑ i : Aligned, coeffNat i)+1 =
    2*((∑ i : Fin 943,selectors i)+(∑ j : Fin 41,copies j))+6 at h
  simp only [selectors,copies,selector_fin_mass,copy_fin_mass] at h
  simpa only [CompactCoefficientMass.stencilMass,CompactCoefficientMass.coefficientMass] using h

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s,f i:ℕ):V) = ∑ i ∈ s,(f i:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Nat.cast_add,ih]

theorem aligned_coefficient_bound : (∑ i : Aligned, coeff (V:=V) i) ≤
    (CompactCoefficientMass.stencilMass:V) := by
  have h := congrArg (fun x : ℕ => (x:V)) aligned_mass_nat
  simp only [Nat.cast_add,Nat.cast_one,cast_sum_generic] at h
  change (∑ i : Aligned, coeff (V:=V) i)+1 = _ at h
  rw [←h]
  exact le_add_of_nonneg_right (by simp)

theorem aligned_family_b1 :
    ((∑ i : Aligned, coeff (V:=V) i*3)+(Exp.exp 67-1))+1 ≤
      ((1:V)+1)*(Exp.exp 67-1) :=
  CompactModelStencilSlack.family_mass_b1 coeff aligned_coefficient_bound

#print axioms CompactConcreteAlignedMass.aligned_mass_nat
#print axioms CompactConcreteAlignedMass.aligned_coefficient_bound
#print axioms CompactConcreteAlignedMass.aligned_family_b1
end CompactConcreteAlignedMass
