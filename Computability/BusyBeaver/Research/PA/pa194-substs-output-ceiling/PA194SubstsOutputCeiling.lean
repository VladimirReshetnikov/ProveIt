import PA194SubstsCeiling
import PA196PASubstitutionUniformGrowth
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
namespace PA194SubstsOutputCeiling
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PA194SubstsCeiling
open PA196PAQVecTowerAlgebra PA196PASubstitutionUniformGrowth
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def outputCeiling (c : M) : M := iter (c+1) (c+3*c+1)

theorem substitution_output_le (c p w : M) (hp : IsUFormula ℒₒᵣ p)
    (hpc : p ≤ c) (hwc : w ≤ c) : subst ℒₒᵣ w p ≤ outputCeiling c := by
  have hseed : seed w p ≤ c+3*c+1 := by
    unfold seed
    exact add_le_add (add_le_add hwc (mul_le_mul' le_rfl hpc)) le_rfl
  have hn : p+1 ≤ c+1 := add_le_add hpc le_rfl
  exact le_trans (subst_le_uniform p hp w)
    (le_trans (iter_seed_mono _ _ _ hseed) (iter_index_mono _ _ _ hn))

theorem common_substitution_witness_ceiling (c : M) :
    ∃ bound : M, ∀ p w : M, IsUFormula ℒₒᵣ p → p ≤ c → w ≤ c →
      (bnd (substsGraph ℒₒᵣ).val).Eval
        (Fin.snoc ![subst ℒₒᵣ w p,w,p] bound) Empty.elim := by
  let ceiling := c + outputCeiling c
  obtain ⟨bound,hbound⟩ := uniform_substs_witness_bound ceiling
  refine ⟨bound,?_⟩
  intro p w hp hpc hwc
  have hout := substitution_output_le c p w hp hpc hwc
  have hcoord : ∀ i, ![subst ℒₒᵣ w p,w,p] i ≤ ceiling := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_trans hout (by simp [ceiling])
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact le_trans hwc (by simp [ceiling])
      · exact Fin.cases (le_trans hpc (by simp [ceiling])) (fun l => Fin.elim0 l) k
  have hgraph : (substsGraph ℒₒᵣ).val.Eval ![subst ℒₒᵣ w p,w,p] Empty.elim := by
    have h := (subst.defined (V := M) (L := ℒₒᵣ)).defined ![subst ℒₒᵣ w p,w,p]
    simpa using h.mpr rfl
  exact hbound _ hcoord hgraph

#print axioms common_substitution_witness_ceiling
#print axioms substitution_output_le
end PA194SubstsOutputCeiling
