import PA196PATermBVGraph
import PA196PABvGrowth

/-! Both witness-bound polarities of the exact arithmetic semiterm recognizer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASemitermBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessTransfer
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_positive : WB M (isSemiterm ℒₒᵣ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PATermBVGraph.wb_termBVGraph (M := M)
  have := PA196PATermBounds.wb_isUTerm_sigma (M := M)
  simp only [isSemiterm, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact wb_exs_term ‘#0’ (fun e y h => by simp at h; exact h.2) (by wb_auto)

theorem wb_negative : WB M (∼(isSemiterm ℒₒᵣ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PATermBVGraph.wb_termBVGraph (M := M)
  have := PA196PATermBounds.wb_isUTerm_neg_pi (M := M)
  simp only [isSemiterm, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  exact wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e b h => ⟨b, by
      have h' := h; simp at h'; rw [h'.1]; exact PA196PABvGrowth.termBV_le_self (e 1), h⟩) (by wb_auto)

#print axioms wb_positive
#print axioms wb_negative
end PA196PASemitermBound
