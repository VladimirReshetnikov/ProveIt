import DiophantineConsistency.PRAWitnessFormulaFunctions
/-! Witness bound for the literal negative pi conjunction-introduction
disjunct of Foundation’s derivation core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessAndRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessFormulaFunctions PRAWitnessTransfer
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ q < D, ∃ dp < D, ∃ dq < D,
    !andIntroGraph D s p q dp dq ∧ (∀ and, !qqAndDef and p q → and ∈ s) ∧
      (∀ c, !fstIdxDef c dp → !insertDef c p s ∧ dp ∈ C) ∧
      (∀ c, !fstIdxDef c dq → !insertDef c q s ∧ dq ∈ C)”
noncomputable def actualAndBranch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or _ (.or _ (.or a _))) => a
  | _ => ⊥
theorem actualAndBranch_eq (T : SetTheory) [T.Δ₁] : actualAndBranch T = branch := by rfl
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
  have := wb_neg_andIntroGraph (M := M)
  have := wb_qqAndDef (M := M)
  have := wb_fstIdxDef (M := M)
  have := wb_neg_insertDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [branch]
  wb_auto
  · refine wb_exs_poly _ (by simp)
      ‘(4+(#3+#2+1)*(#3+#2+1)+1)*(4+(#3+#2+1)*(#3+#2+1)+1)+1’
      (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    rw [h'.1]
    simpa [qqAnd, Semiterm.val_func, numeral_eq_natCast] using code3_le (4 : V) (e 3) (e 2)
  · refine wb_exs_poly _ (by simp) ‘#1’ (fun V _ _ e c h => ⟨c, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    simp [h'.1]
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    simp [h'.1]
theorem wb_neg_actualAndBranch (T : SetTheory) [T.Δ₁] : WB M (∼actualAndBranch T) := by
  rw [actualAndBranch_eq]
  exact wb_neg_branch
end DiophantineConsistency.PRAWitnessAndRuleBranch
