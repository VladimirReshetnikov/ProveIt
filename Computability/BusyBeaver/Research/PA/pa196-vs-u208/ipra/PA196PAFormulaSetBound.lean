import PA196PABvGrowth
import DiophantineConsistency.PRAWitnessFormulaSet
import DiophantineConsistency.PRAWitnessDerivationCoreLeft

/-! Bounds for the actual PA formula-set conjunct, conditional only on a
witness bound for the arithmetic-language bound-variable graph. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAFormulaSetBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
open PRAWitnessTransfer PA196PABvGrowth PA196PAFormulaComplete

noncomputable def actualSigmaLeft : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and left _ => left
  | _ => ⊥
noncomputable def actualPiLeft : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and left _ => left
  | _ => ⊥
noncomputable def sigmaLeft : ArithmeticSemisentence 2 :=
  “d C. ∃ fst, !fstIdxDef fst d ∧ !(isFormulaSet ℒₒᵣ).sigma fst”
noncomputable def piLeft : ArithmeticSemisentence 2 :=
  “d C. ∀ fst, !fstIdxDef fst d → !(isFormulaSet ℒₒᵣ).pi fst”
theorem actualSigmaLeft_eq : actualSigmaLeft = sigmaLeft := by rfl
theorem actualPiLeft_eq : actualPiLeft = piLeft := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_isSemiformula_sigma (hb : WB M (bvGraph ℒₒᵣ).val) : WB M (isSemiformula ℒₒᵣ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hb; have := wb_isUFormula_sigma (M := M)
  simp only [isSemiformula, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact wb_exs_term ‘#0’ (fun e y h => by simp at h; exact h.2) (by wb_auto)

theorem wb_isSemiformula_neg_pi (hb : WB M (bvGraph ℒₒᵣ).val) : WB M (∼(isSemiformula ℒₒᵣ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hb; have := wb_isUFormula_neg_pi (M := M)
  simp only [isSemiformula, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  exact wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e b h => ⟨b, by
      have h' := h; simp at h'; rw [h'.1]; exact bv_le_self (e 1), h⟩) (by wb_auto)

theorem wb_isFormulaSet_sigma (hb : WB M (bvGraph ℒₒᵣ).val) : WB M (isFormulaSet ℒₒᵣ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_isSemiformula_sigma hb; have := wb_bitDef (M := M); have := wb_neg_bitDef (M := M)
  simp only [isFormulaSet, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_isFormulaSet_neg_pi (hb : WB M (bvGraph ℒₒᵣ).val) : WB M (∼(isFormulaSet ℒₒᵣ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_isSemiformula_neg_pi hb; have := wb_bitDef (M := M); have := wb_neg_bitDef (M := M)
  simp only [isFormulaSet, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto

theorem wb_actualSigmaLeft (hb : WB M (bvGraph ℒₒᵣ).val) : WB M actualSigmaLeft := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [actualSigmaLeft_eq]
  have := wb_fstIdxDef (M := M); have := wb_isFormulaSet_sigma hb
  simp only [sigmaLeft]
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e fst h => ⟨fst, ?_, h⟩) (by wb_auto)
  have h' := h; simp at h'; simp [h'.1]

theorem wb_neg_actualPiLeft (hb : WB M (bvGraph ℒₒᵣ).val) : WB M (∼actualPiLeft) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [actualPiLeft_eq]
  have := wb_fstIdxDef (M := M); have := wb_isFormulaSet_neg_pi hb
  simp only [piLeft, Semiformula.neg_all, Semiformula.imp_eq, DeMorgan.or, DeMorgan.neg]
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e fst h => ⟨fst, ?_, h⟩) (by wb_auto)
  have h' := h; simp at h'; simp [h'.1]

#print axioms wb_actualSigmaLeft
#print axioms wb_neg_actualPiLeft
end PA196PAFormulaSetBound
