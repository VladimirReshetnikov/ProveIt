import DiophantineConsistency.PRAWitnessSubsts
import DiophantineConsistency.PRAWitnessSubstsExistential
/-! Witness bound for the literal negative pi existential-introduction
disjunct of Foundation’s derivation core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessExsRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessFormulaFunctions PRAWitnessTermFunctions PRAWitnessTransfer PRAWitnessSubsts PRAWitnessSubstsExistential
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ t < D, ∃ dp < D,
    !exsIntroGraph D s p t dp ∧ (∀ ex, !qqExsDef ex p → ex ∈ s) ∧
    !(isSemiterm ℒₛₑₜ).pi 0 t ∧
    ∀ c, !fstIdxDef c dp → ∀ pt, !(substs1Graph ℒₛₑₜ) pt t p → !insertDef c pt s ∧ dp ∈ C”
noncomputable def actualExsBranch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or a _)))))) => a
  | _ => ⊥
theorem actualExsBranch_eq (T : SetTheory) [T.Δ₁] : actualExsBranch T = branch := by rfl
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
  have := wb_neg_exsIntroGraph (M := M)
  have := wb_qqExsDef (M := M)
  have := wb_isSemiterm_neg_pi (M := M)
  have := wb_fstIdxDef (M := M)
  have := wb_substs1Graph (M := M)
  have := wb_neg_insertDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [branch]
  wb_auto
  · refine wb_exs_poly _ (by simp) ‘(7+#2+1)*(7+#2+1)+1’
      (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    rw [h'.1]
    simpa [qqExs, Semiterm.val_func, numeral_eq_natCast] using code2_le (7 : V) (e 2)
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) ?_
    · have h' := h
      simp at h'
      simp [h'.1]
    · wb_auto
      refine wb_exs_substs1 (2 : Fin 7) (3 : Fin 7) _ (by simp) (by wb_auto) ?_
      intro V _ _ e y h
      have h' := h
      simp at h' ⊢
      exact h'.1
theorem wb_neg_actualExsBranch (T : SetTheory) [T.Δ₁] : WB M (∼actualExsBranch T) := by
  rw [actualExsBranch_eq]
  exact wb_neg_branch
end DiophantineConsistency.PRAWitnessExsRuleBranch
