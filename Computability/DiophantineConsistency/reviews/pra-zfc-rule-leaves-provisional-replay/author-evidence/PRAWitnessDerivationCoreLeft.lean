import DiophantineConsistency.PRAWitnessFormulaSetCandidate
import DiophantineConsistency.PRAWitnessTransfer

/-! Bounds for the formula-set conjunct of the actual derivation core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessDerivationCoreLeft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessTransfer

noncomputable def sigmaLeft : ArithmeticSemisentence 2 :=
  “d C. ∃ fst, !fstIdxDef fst d ∧ !(isFormulaSet ℒₛₑₜ).sigma fst”
noncomputable def piLeft : ArithmeticSemisentence 2 :=
  “d C. ∀ fst, !fstIdxDef fst d → !(isFormulaSet ℒₛₑₜ).pi fst”
noncomputable def actualSigmaLeft (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with
  | .and left _ => left
  | _ => ⊥
noncomputable def actualPiLeft (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and left _ => left
  | _ => ⊥
noncomputable def sigmaTail (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with
  | .and _ tail => tail
  | _ => ⊥
noncomputable def piTail (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ tail => tail
  | _ => ⊥

theorem actualSigmaLeft_eq (T : SetTheory) [T.Δ₁] : actualSigmaLeft T = sigmaLeft := by rfl
theorem actualPiLeft_eq (T : SetTheory) [T.Δ₁] : actualPiLeft T = piLeft := by rfl
theorem coreSigma_eq (T : SetTheory) [T.Δ₁] :
    (Derivation.blueprint T).core.sigma.val = sigmaLeft ⋏ sigmaTail T := by rfl
theorem corePi_eq (T : SetTheory) [T.Δ₁] :
    (Derivation.blueprint T).core.pi.val = piLeft ⋏ piTail T := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_sigmaLeft : WB M sigmaLeft := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_fstIdxDef (M := M)
  have := PRAWitnessFormulaSetCandidate.wb_isFormulaSet_sigma (M := M)
  simp only [sigmaLeft]
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e fst h => ⟨fst, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  simp [h'.1]

theorem wb_neg_piLeft : WB M (∼piLeft) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_fstIdxDef (M := M)
  have := PRAWitnessFormulaSetCandidate.wb_isFormulaSet_neg_pi (M := M)
  simp only [piLeft, Semiformula.neg_all, Semiformula.imp_eq, DeMorgan.or, DeMorgan.neg]
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e fst h => ⟨fst, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  simp [h'.1]

theorem wb_actualSigmaLeft (T : SetTheory) [T.Δ₁] : WB M (actualSigmaLeft T) := by
  rw [actualSigmaLeft_eq]
  exact wb_sigmaLeft

theorem wb_neg_actualPiLeft (T : SetTheory) [T.Δ₁] : WB M (∼actualPiLeft T) := by
  rw [actualPiLeft_eq]
  exact wb_neg_piLeft

/-- The sigma core now needs only its rule-disjunction bound. -/
theorem wb_coreSigma_of_tail (T : SetTheory) [T.Δ₁] (h : WB M (sigmaTail T)) :
    WB M (Derivation.blueprint T).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [coreSigma_eq]
  exact wb_and wb_sigmaLeft h

/-- The negative pi core now needs only the negated rule-disjunction bound. -/
theorem wb_neg_corePi_of_tail (T : SetTheory) [T.Δ₁] (h : WB M (∼piTail T)) :
    WB M (∼(Derivation.blueprint T).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [corePi_eq]
  simpa only [DeMorgan.and] using wb_or wb_neg_piLeft h
end DiophantineConsistency.PRAWitnessDerivationCoreLeft
