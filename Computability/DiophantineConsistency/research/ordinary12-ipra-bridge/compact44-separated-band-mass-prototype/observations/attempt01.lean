import DiophantineConsistency.CompactCoefficientMass
import DiophantineConsistency.CompactModelStencilSlack
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactAlignedFamilyDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two separate bands and five separately retained bare/spatial terms. -/
abbrev Aligned := (Fin 943 ⊕ Fin 41) ⊕ ((Fin 943 ⊕ Fin 41) ⊕ Fin 5)

def bandCoeffNat : Fin 943 ⊕ Fin 41 → ℕ
  | .inl i => CompactCoefficientMass.selector (Compact943Data.row i)
  | .inr j => 2^(10+j.val)

def coeffNat : Aligned → ℕ
  | .inl i => bandCoeffNat i
  | .inr (.inl i) => bandCoeffNat i
  | .inr (.inr _) => 1

def coeff (i : Aligned) : V := (coeffNat i:V)

/-- A proposed non-expanding bridge from the finite selector indexing to the audited list. -/
theorem rows_ofFn : List.ofFn Compact943Data.row = Compact943Data.rows := by
  calc
    List.ofFn Compact943Data.row =
        List.ofFn (fun i : Fin Compact943Data.rows.length =>
          Compact943Data.row (Fin.cast Compact943Data.rows_length i)) :=
      List.ofFn_congr Compact943Data.rows_length.symm Compact943Data.row
    _ = List.ofFn (Compact943Data.rows.get) := by
      congr 1
      funext i
      cases i
      rfl
    _ = Compact943Data.rows := List.ofFn_get _

theorem selector_fin_mass :
    (∑ i : Fin 943, CompactCoefficientMass.selector (Compact943Data.row i)) =
      CompactCoefficientMass.selectorMass := by
  rw [← Fin.sum_ofFn]
  rw [List.ofFn_comp', rows_ofFn]
  rfl

theorem copy_fin_mass :
    (∑ j : Fin 41, 2^(10+j.val) : ℕ) = CompactCoefficientMass.copyMass := by
  rw [CompactCoefficientMass.copy_mass_exact]
  decide

theorem aligned_mass_nat : (∑ i : Aligned, coeffNat i)+1 =
    CompactCoefficientMass.stencilMass := by
  simp only [Fintype.sum_sum_type, coeffNat, bandCoeffNat]
  rw [selector_fin_mass,copy_fin_mass,selector_fin_mass,copy_fin_mass]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [CompactCoefficientMass.stencilMass, CompactCoefficientMass.coefficientMass]
  ring

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

#print axioms CompactAlignedFamilyDraft.rows_ofFn
#print axioms CompactAlignedFamilyDraft.selector_fin_mass
#print axioms CompactAlignedFamilyDraft.copy_fin_mass
#print axioms CompactAlignedFamilyDraft.aligned_mass_nat
#print axioms CompactAlignedFamilyDraft.aligned_coefficient_bound
#print axioms CompactAlignedFamilyDraft.aligned_family_b1
end CompactAlignedFamilyDraft
