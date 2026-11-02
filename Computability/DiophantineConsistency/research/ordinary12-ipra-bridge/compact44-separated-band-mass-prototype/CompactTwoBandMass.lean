import DiophantineConsistency.CompactSelectorMassBridge
import DiophantineConsistency.CompactModelStencilSlack
set_option autoImplicit false
set_option Elab.async false
noncomputable section
attribute [local irreducible] Compact943Data.rows
namespace CompactTwoBandMass
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactSelectorMassBridge
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s,f i:ℕ):V) = ∑ i ∈ s,(f i:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Nat.cast_add,ih]

theorem selector_model_mass :
    (∑ i : Fin 943, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V)) =
      (CompactCoefficientMass.selectorMass:V) := by
  have h := congrArg (fun x : ℕ => (x:V)) selector_fin_mass
  simpa only [cast_sum_generic] using h

theorem copy_model_mass :
    (∑ j : Fin 41, ((2^(10+j.val):ℕ):V)) = (CompactCoefficientMass.copyMass:V) := by
  have h := congrArg (fun x : ℕ => (x:V)) copy_fin_mass
  simpa only [cast_sum_generic] using h

/-- Exact coefficient mass of two separately retained bands and five unit words. -/
theorem two_band_plus_temporal_mass :
    2*((∑ i : Fin 943, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V))+
       (∑ j : Fin 41, ((2^(10+j.val):ℕ):V)))+5+1 =
      (CompactCoefficientMass.stencilMass:V) := by
  rw [selector_model_mass,copy_model_mass]
  unfold CompactCoefficientMass.stencilMass CompactCoefficientMass.coefficientMass
  push_cast
  ring

/-- The exact split-band expression meets the b=1 heterogeneous mass bound. -/
theorem split_band_mass_b1 :
    (2*((∑ i : Fin 943, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V))+
       (∑ j : Fin 41, ((2^(10+j.val):ℕ):V)))+5)*3+(Exp.exp 67-1)+1 ≤
      ((1:V)+1)*(Exp.exp 67-1) := by
  have he := two_band_plus_temporal_mass (V:=V)
  have hcoeff : 2*((∑ i : Fin 943, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V))+
       (∑ j : Fin 41, ((2^(10+j.val):ℕ):V)))+5 ≤ (CompactCoefficientMass.stencilMass:V) := by
    rw [←he]
    exact le_add_of_nonneg_right (by simp)
  have hthree := mul_le_mul_of_nonneg_right hcoeff (by simp : (0:V)≤3)
  have hslack := CompactModelStencilSlack.stencil_mass_b1 (V:=V)
  calc
    _ ≤ (CompactCoefficientMass.stencilMass:V)*3+(Exp.exp 67-1)+1 :=
      add_le_add_left (add_le_add_left hthree _) _
    _ ≤ _ := by simpa only [mul_comm] using hslack

#print axioms CompactTwoBandMass.selector_model_mass
#print axioms CompactTwoBandMass.copy_model_mass
#print axioms CompactTwoBandMass.two_band_plus_temporal_mass
#print axioms CompactTwoBandMass.split_band_mass_b1
end CompactTwoBandMass
