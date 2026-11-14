import PA196PASubstitutionWitnessComplete
import PA196PASubstitutionTotalGrowth

/-! Arithmetic one-term substitution graph witness bound and a total numeric
tower bound for its value. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASubstitutionOne
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessTransfer PRAWitnessTermFunctions PA196PASubstitutionTotalGrowth PA196PAQVecTowerAlgebra

section arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem singleton_le (t : V) : (?[t] : V) ≤ (t+1)*(t+1)+1 := by
  rw [show (?[t] : V) = adjoin t 0 from rfl, adjoin_def]
  simpa using add_le_add (pair_le_sq (le_refl t) (le_refl (0:V))) (le_refl 1)

theorem substs1_le_tower (t p : V) :
    substs1 ℒₒᵣ t p ≤ iter (p+((t+1)*(t+1)+1)+2)
      (4*(p+((t+1)*(t+1)+1))+1) := by
  have hs := singleton_le t
  have hp : p+(?[t] : V) ≤ p+((t+1)*(t+1)+1) := add_le_add le_rfl hs
  have h := subst_le_tower (?[t] : V) p
  exact le_trans h (le_trans (iter_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl hp) le_rfl))
    (iter_index_mono _ _ _ (add_le_add hp le_rfl)))
end arithmetic

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_substs1Graph : WB M (substs1Graph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PASubstitutionWitnessComplete.wb_substsGraph (M := M)
  have := PRAWitnessArithmetic.wb_adjoinDef (M := M)
  simp only [substs1Graph, HierarchySymbol.Semiformula.val_mkSigma]
  exact wb_exs_poly _ (by simp) ‘(#1 + 1) * (#1 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1, adjoin_def]
      simpa using add_le_add (pair_le_sq (le_refl (e 1)) (le_refl 0)) (le_refl 1), h⟩) (by wb_auto)
end models

#print axioms singleton_le
#print axioms substs1_le_tower
#print axioms wb_substs1Graph
end PA196PASubstitutionOne
