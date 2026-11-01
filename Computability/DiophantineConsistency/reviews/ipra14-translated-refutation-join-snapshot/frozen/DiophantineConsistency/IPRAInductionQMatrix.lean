import DiophantineConsistency.IPRAInductionGGClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRAMatrixQ
variable {L : Language} [L.ORing]
theorem matrix_var_bound (φ : Semiformula L ℕ 1) (x : ℕ) (hx : φ.FVar? x) :
    x < (succInd φ).fvSup := by
  apply Semiformula.lt_fvSup_of_fvar?
  simp [succInd, Semiformula.FVar?, hx]
theorem fixed_matrix_no_free (φ : Semiformula L ℕ 1) :
    ((Rew.fixitr 0 (succInd φ).fvSup).q ▹ φ : Semiformula L ℕ ((0 + (succInd φ).fvSup) + 1)).freeVariables = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have h : ((Rew.fixitr 0 (succInd φ).fvSup).q ▹ φ : Semiformula L ℕ ((0 + (succInd φ).fvSup) + 1)).FVar? x := hx
  rcases Semiformula.fvar?_rew h with (⟨z, hz⟩ | ⟨z, hz, hx'⟩)
  · cases z using Fin.cases <;> simp at hz
  · have hb := matrix_var_bound φ z hz
    simp [Rew.q_fvar, Rew.fixitr_fvar, hb] at hx'

def finiteMatrix (φ : Semiformula L ℕ 1) : Semisentence L ((0 + (succInd φ).fvSup) + 1) :=
    (((Rew.fixitr 0 (succInd φ).fvSup).q ▹ φ).toEmpty (fixed_matrix_no_free φ))

theorem finiteMatrix_open (φ : Semiformula L ℕ 1) (h : φ.Open) : (finiteMatrix φ).Open := by
  have he : ((Rew.fixitr 0 (succInd φ).fvSup).q ▹ φ : Semiformula L ℕ ((0 + (succInd φ).fvSup) + 1)).Open := by simpa using h
  have he' : (Rewriting.emb (finiteMatrix φ) : Semiformula L ℕ ((0 + (succInd φ).fvSup) + 1)).Open := by simpa [finiteMatrix] using he
  simpa only [Semiformula.rew_open_iff] using he'
theorem native_matrix_instance (φ : Semiformula PRALanguage.language ℕ 1) (h : φ.Open) :
    IPRANativeInduction.inductionAxiom (finiteMatrix φ)ᴺ ∈ IPRANativeInduction.nativeInduction :=
  IPRANativeInduction.translated_matrix_nativeInduction (finiteMatrix φ) (finiteMatrix_open φ h)
theorem emb_gg_finiteMatrix (φ : Semiformula L ℕ 1) :
    (Rewriting.emb (finiteMatrix φ)ᴺ : Semiformulaᵢ L ℕ ((0 + (succInd φ).fvSup) + 1)) =
      (Rew.fixitr 0 (succInd φ).fvSup).q ▹ φᴺ := by
  simp only [finiteMatrix, Semiformula.emb_toEmpty,
    Semiformula.rew_doubleNegation]
end DiophantineConsistency.IPRAMatrixQ
