import DiophantineConsistency.PRAWitnessFormulaFunctions
/-! Witness bound for the literal negative pi verum-introduction disjunct
of Foundation’s `Derivation.blueprint`, with its syntactic identity checked. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessVerumRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessFormulaFunctions PRAWitnessTransfer
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, !verumIntroGraph D s ∧ ∀ vrm, !qqVerumDef vrm → vrm ∈ s”
noncomputable def actualVerumBranch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or _ (.or vrm _)) => vrm
  | _ => ⊥
theorem actualVerumBranch_eq (T : SetTheory) [T.Δ₁] : actualVerumBranch T = branch := by rfl
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_neg_branch : WB M (∼branch) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_neg_verumIntroGraph (M := M)
  have := wb_qqVerumDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [branch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘10’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  rw [h'.1]
  have hbound := code2_le (2 : V) 0
  have hconst : ((2 : V) + 0 + 1) * (2 + 0 + 1) + 1 = 10 := by norm_num
  rw [hconst] at hbound
  simpa [qqVerum, Semiterm.val_func, numeral_eq_natCast] using hbound
theorem wb_neg_actualVerumBranch (T : SetTheory) [T.Δ₁] : WB M (∼actualVerumBranch T) := by
  rw [actualVerumBranch_eq]
  exact wb_neg_branch
end DiophantineConsistency.PRAWitnessVerumRuleBranch
