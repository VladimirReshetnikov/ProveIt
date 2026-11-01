import DiophantineConsistency.IPRAReconstructAlgebra
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReconstructClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRAPredReconstruct IPRAAddRecursion IPRASubArithmetic IPRAReconstructAlgebra
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def matrix : Semisentenceᵢ language 2 :=
  (.rel .eq ![.func subCode ![#1,#0], zeroTerm 2]) ⋎
  (.rel .eq ![.func addCode ![#0,.func subCode ![#1,#0]],#1])
theorem matrix_open : IPRAQuantifierFree.OpenI matrix := by simp [matrix, IPRAQuantifierFree.OpenI]

theorem var_zero : Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = (&0 : SyntacticTerm language) := by
  rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
theorem var_one : Rew.free (Rew.free (#(1 : Fin 2) : Semiterm language ℕ 2)) = (&1 : SyntacticTerm language) := by
  change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
  rw [Rew.free_bvar_last, Rew.free_fvar]

theorem matrix_free2 : Rewriting.free (Rewriting.free (Rewriting.emb matrix)) = I (&0) (&1) := by
  simp [matrix, I, Z, R, IPRASubArithmetic.sub, add, z, equal, zeroTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => simp [Rew.func, Matrix.fun_eq_vec_two, var_one]
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Matrix.fun_eq_vec_two, var_one] <;> funext j <;> exact Fin.elim0 j
    | succ i => exact Fin.elim0 i

theorem matrix_step_free2 : Rewriting.free (Rewriting.free (Rewriting.emb (atStep matrix))) = I (add (&0) one) (&1) := by
  simp [matrix, I, Z, R, IPRASubArithmetic.sub, add, z, one, equal, zeroTerm, atStep, stepTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff]; change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1; exact var_one
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff] <;> change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1 <;> exact var_one
    | succ i => exact Fin.elim0 i
theorem shift_embedded {n : ℕ} (φ : Semisentenceᵢ language n) :
    Rewriting.shift (Rewriting.emb φ) = Rewriting.emb φ := by
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

theorem step_closed : F ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ (Rewriting.emb matrix 🡒 Rewriting.emb (atStep matrix)) := by
  have hF : F⁺ = F := by
    simp [F, leftAx, zeroDecAx, predReconAx, zeroLeftAx, shift_embedded, E, subBaseAx, subStepAx, predBaseAx, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hF]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hF]
  have ho := Classical.choice (reconstruction_step_open (&0) (&1))
  convert ho using 1
  have h1 := matrix_free2
  have h2 := matrix_step_free2
  simp [matrix, I, Z, R, IPRASubArithmetic.sub, add, z, equal, zeroTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel] at h1
  simp [matrix, I, Z, R, IPRASubArithmetic.sub, add, z, one, equal, zeroTerm, atStep, stepTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel] at h2
  simpa [matrix, I, Z, R, IPRASubArithmetic.sub, add, z, one, equal, zeroTerm, atStep, stepTerm, Rewriting.free, Rewriting.emb,
    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def] using And.intro h1 h2
theorem base_closed : F ⊢[𝗜𝗻𝘁¹] ∀⁰ Rewriting.emb (atZero matrix) := by
  have hF : F⁺ = F := by
    simp [F, leftAx, zeroDecAx, predReconAx, zeroLeftAx, shift_embedded, E, subBaseAx, subStepAx, predBaseAx, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hF]
  have ho := Classical.choice (reconstruction_base_open (&0))
  convert ho using 1
  simp [matrix, I, Z, R, IPRASubArithmetic.sub, add, z, equal, atZero, zeroTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff]; change Rew.free (#(0 : Fin 1) : Semiterm language ℕ 1) = &0; rw [Rew.free_bvar_last_zero]
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff] <;> change Rew.free (#(0 : Fin 1) : Semiterm language ℕ 1) = &0 <;> rw [Rew.free_bvar_last_zero]
    | succ i => exact Fin.elim0 i
theorem f_theory (φ : Propositionᵢ language) (h : F ⊢[𝗜𝗻𝘁¹] φ) :
    (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] φ := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hF : ∀ p ∈ F, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [F, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp
    · exact IPRASuccLeft.successor_left
    · exact IPRAZeroStepNative.zero_decidable
    · exact IPRAPredReconstruct.reconstruction
    · exact IPRAZeroLeft.zero_left
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCode (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCode (1 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix subCode (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix subCode (1 : Fin 2))))
    · exact IPRASubArithmetic.e_theory p ⟨FiniteContext.byAxm hp⟩
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀F := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hF
  exact ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice h))) (Classical.choice hc)⟩

theorem base_native : nativeTheory ⊢ ∀⁰ atZero matrix := by
  have hi := Classical.choice (f_theory _ base_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹]
    Rewriting.emb (∀⁰ atZero matrix)
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]

theorem step_native : nativeTheory ⊢ ∀⁰ ∀⁰ (matrix 🡒 atStep matrix) := by
  have hi := Classical.choice (f_theory _ step_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹]
    Rewriting.emb (∀⁰ ∀⁰ (matrix 🡒 atStep matrix))
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]
theorem reconstruction : nativeTheory ⊢ ∀⁰ ∀⁰ matrix := by
  have hi : nativeTheory ⊢ ∀⁰ (atZero matrix 🡒 ((∀⁰ (matrix 🡒 atStep matrix)) 🡒 ∀⁰ matrix)) := by
    have hh : nativeTheory ⊢ inductionAxiom matrix :=
      IPRANativeAxiomImage.native_axiom (NativeAxiom.induction ⟨1, matrix, matrix_open, rfl⟩)
    simpa [inductionAxiom, inductionBody, allClosure_succ] using hh
  have hstep : nativeTheory ⊢ ∀⁰ ((∀⁰ (matrix 🡒 atStep matrix)) 🡒 ∀⁰ matrix) :=
    IPRASuccLeft.all_mdp (atZero matrix) _ hi base_native
  exact IPRASuccLeft.all_mdp (∀⁰ (matrix 🡒 atStep matrix)) (∀⁰ matrix) hstep step_native
end DiophantineConsistency.IPRAReconstructClosure
