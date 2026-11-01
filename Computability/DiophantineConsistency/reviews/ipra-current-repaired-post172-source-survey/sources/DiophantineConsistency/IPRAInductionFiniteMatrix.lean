import DiophantineConsistency.IPRAInductionGGClosure
/-! Construct the finite-parameter open matrix corresponding to an actual
Foundation induction matrix. Matching its closed induction instance with
Foundation's translated induction axiom remains a separate obligation. -/
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRAMatrix
variable {L : Language} [L.ORing]
theorem matrix_var_bound (φ : Semiformula L ℕ 1) (x : ℕ) (hx : φ.FVar? x) :
    x < (succInd φ).fvSup := by
  apply Semiformula.lt_fvSup_of_fvar?
  simp [succInd, Semiformula.FVar?, hx]
theorem fixed_matrix_no_free (φ : Semiformula L ℕ 1) :
    (Rew.fixitr 1 (succInd φ).fvSup ▹ φ : Semiformula L ℕ (1 + (succInd φ).fvSup)).freeVariables = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have h : (Rew.fixitr 1 (succInd φ).fvSup ▹ φ : Semiformula L ℕ (1 + (succInd φ).fvSup)).FVar? x := hx
  rw [Rew.eq_bind (Rew.fixitr 1 (succInd φ).fvSup)] at h
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar] at h
  rcases Semiformula.fvar?_rew h with (⟨z, hz⟩ | ⟨z, hz, hx'⟩)
  · simp at hz
  · have hb := matrix_var_bound φ z hz
    simp [hb] at hx'
def finiteMatrix (φ : Semiformula L ℕ 1) : Semisentence L ((succInd φ).fvSup + 1) :=
  cast (by rw [Nat.add_comm 1])
    ((Rew.fixitr 1 (succInd φ).fvSup ▹ φ).toEmpty (fixed_matrix_no_free φ))

omit [L.ORing] in
theorem cast_open {n m : ℕ} (e : n = m) (p : Semisentence L n) :
    (cast (congrArg (Semisentence L) e) p).Open ↔ p.Open := by cases e; rfl

theorem finiteMatrix_open (φ : Semiformula L ℕ 1) (h : φ.Open) : (finiteMatrix φ).Open := by
  have he : (Rew.fixitr 1 (succInd φ).fvSup ▹ φ : Semiformula L ℕ (1 + (succInd φ).fvSup)).Open := by simpa using h
  have he' : ((Rew.fixitr 1 (succInd φ).fvSup ▹ φ).toEmpty (fixed_matrix_no_free φ)).Open := by
    have h'' : (Rewriting.emb ((Rew.fixitr 1 (succInd φ).fvSup ▹ φ).toEmpty (fixed_matrix_no_free φ)) : Semiformula L ℕ (1 + (succInd φ).fvSup)).Open := by simpa using he
    simpa only [Semiformula.rew_open_iff] using h''
  exact (cast_open (Nat.add_comm 1 (succInd φ).fvSup) _).2 he'
theorem native_matrix_instance (φ : Semiformula PRALanguage.language ℕ 1) (h : φ.Open) :
    IPRANativeInduction.inductionAxiom (finiteMatrix φ)ᴺ ∈ IPRANativeInduction.nativeInduction :=
  IPRANativeInduction.translated_matrix_nativeInduction (finiteMatrix φ) (finiteMatrix_open φ h)
end DiophantineConsistency.IPRAMatrix
