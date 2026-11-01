import DiophantineConsistency.IPRAFunctionCongruenceOpen
/-! Exact bound-variable binding and native proof for arbitrary-arity function
congruence. The GG image is provided by a separate checked client. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAFunctionCongruenceClosed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory IPRAAllSpecialize IPRAFunctionCongruenceOpen
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def leftVec {k : ℕ} (i : Fin k) : SyntacticTerm language := &i.val
def rightVec {k : ℕ} (i : Fin k) : SyntacticTerm language := &(i.val + k)

def sourceBody {k : ℕ} (f : language.Func k) : Semisentenceᵢ language (k+k) :=
  (Matrix.conj fun i : Fin k =>
    Semiformulaᵢ.rel Language.ORing.Rel.eq ![#(i.castAdd k), #(i.addNat k)]) 🡒
    Semiformulaᵢ.rel Language.ORing.Rel.eq
      ![Semiterm.func f (fun i => #(i.castAdd k)),
        Semiterm.func f (fun i => #(i.addNat k))]

def sourceDirect {k : ℕ} (f : language.Func k) : Sentenceᵢ language := ∀⁰* sourceBody f

theorem closed_open_form {k : ℕ} (f : language.Func k) :
    functionContext f ⊢[𝗜𝗻𝘁¹] ∀⁰* (Rew.fixitr 0 (k+k) ▹
      ((Matrix.conj fun i : Fin k => equal (leftVec i) (rightVec i)) 🡒
      equal (Semiterm.func f leftVec) (Semiterm.func f rightVec))) :=
  allClosure_fixitr_context (functionContext f) (functionContext_shift f)
    (function_conj_open f leftVec rightVec) (k+k)
theorem cast_bvar {n m : ℕ} (h : n = m) (i : Fin n) :
    cast (congrArg (Semiterm language ℕ) h) (#i) = #(Fin.cast h i) := by
  cases h
  rfl

theorem fix_left {k : ℕ} (i : Fin k) :
    cast (congrArg (Semiterm language ℕ) (Nat.zero_add (k+k)))
      (Rew.fixitr 0 (k+k) (leftVec i)) =
      Rew.emb (#(i.castAdd k) : TermN (k+k)) := by
  have hi : i.val < k+k := by omega
  simp only [leftVec, Rew.fixitr_fvar, dif_pos hi, Rew.emb_bvar]
  rw [cast_bvar (Nat.zero_add (k+k))]
  congr 1
  apply Fin.ext
  simp

theorem fix_right {k : ℕ} (i : Fin k) :
    cast (congrArg (Semiterm language ℕ) (Nat.zero_add (k+k)))
      (Rew.fixitr 0 (k+k) (rightVec i)) =
      Rew.emb (#(i.addNat k) : TermN (k+k)) := by
  have hi : i.val + k < k+k := by omega
  simp only [rightVec, Rew.fixitr_fvar, dif_pos hi, Rew.emb_bvar]
  rw [cast_bvar (Nat.zero_add (k+k))]
  congr 1
  apply Fin.ext
  simp
theorem cast_formula {n m : ℕ} (h : n = m) (p : Semiformulaᵢ language ℕ n) :
    cast (congrArg (Semiformulaᵢ language ℕ) h) p = Rew.cast h ▹ p := by
  cases h
  simp

theorem cast_term {n m : ℕ} (h : n = m) (t : Semiterm language ℕ n) :
    cast (congrArg (Semiterm language ℕ) h) t = Rew.cast h t := by
  cases h
  simp
theorem bound_function_matrix {k : ℕ} (f : language.Func k) :
    cast (congrArg (Semiformulaᵢ language ℕ) (Nat.zero_add (k+k)))
      (Rew.fixitr 0 (k+k) ▹
        ((Matrix.conj fun i : Fin k => equal (leftVec i) (rightVec i)) 🡒
          equal (Semiterm.func f leftVec) (Semiterm.func f rightVec))) =
      Rewriting.emb (sourceBody f) := by
  rw [cast_formula (Nat.zero_add (k+k)), ← TransitiveRewriting.comp_app]
  simp [sourceBody, equal, Semiformulaᵢ.rew_rel,
    Rew.comp_app, ← cast_term (Nat.zero_add (k+k)), Function.comp_def]
  constructor
  · congr 1
    funext i
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => exact fix_left i
    | succ j => cases j using Fin.cases with
      | zero => exact fix_right i
      | succ j => exact Fin.elim0 j
  · funext j
    cases j using Fin.cases with
    | zero =>
      change cast (congrArg (Semiterm language ℕ) (Nat.zero_add (k+k)))
        (Rew.fixitr 0 (k+k) (Semiterm.func f leftVec)) =
        Rew.emb (Semiterm.func f (fun i => #(i.castAdd k)))
      rw [cast_term (Nat.zero_add (k+k))]
      simp only [Rew.func]
      congr 1
      funext i
      simpa only [Function.comp_def, ← cast_term (Nat.zero_add (k+k))] using fix_left i
    | succ j => cases j using Fin.cases with
      | zero =>
        change cast (congrArg (Semiterm language ℕ) (Nat.zero_add (k+k)))
          (Rew.fixitr 0 (k+k) (Semiterm.func f rightVec)) =
          Rew.emb (Semiterm.func f (fun i => #(i.addNat k)))
        rw [cast_term (Nat.zero_add (k+k))]
        simp only [Rew.func]
        congr 1
        funext i
        simpa only [Function.comp_def, ← cast_term (Nat.zero_add (k+k))] using fix_right i
      | succ j => exact Fin.elim0 j
theorem closure_binding {k : ℕ} (f : language.Func k) :
    (∀⁰* (Rew.fixitr 0 (k+k) ▹
      ((Matrix.conj fun i : Fin k => equal (leftVec i) (rightVec i)) 🡒
        equal (Semiterm.func f leftVec) (Semiterm.func f rightVec)))) =
      (Rewriting.emb (sourceDirect f) : Propositionᵢ language) := by
  have h := IPRANativeEquationImages.allClosure_cast (Nat.zero_add (k+k))
    (Rew.fixitr 0 (k+k) ▹
      ((Matrix.conj fun i : Fin k => equal (leftVec i) (rightVec i)) 🡒
        equal (Semiterm.func f leftVec) (Semiterm.func f rightVec)))
  rw [← h, bound_function_matrix, ← Rewriting.emb_allClosure]
  rfl

theorem function_closed_context {k : ℕ} (f : language.Func k) :
    functionContext f ⊢[𝗜𝗻𝘁¹] (Rewriting.emb (sourceDirect f) : Propositionᵢ language) := by
  rw [← closure_binding]
  exact closed_open_form f
theorem function_native {k : ℕ} (f : language.Func k) : nativeTheory ⊢ sourceDirect f := by
  let Γ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : ∀ p ∈ functionContext f, Γ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [functionContext, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_ofFn] at hp
    rcases hp with (rfl | rfl) | ⟨i, rfl⟩
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality
        (EqualityAxiomI.substitution IPRAEqualityTransGG.matrix))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality
        (EqualityAxiomI.substitution (funMatrix f i)))
  have hc : Γ *⊢[𝗜𝗻𝘁¹] ⋀(functionContext f) := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hax
  change Γ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb (sourceDirect f) : Propositionᵢ language)
  exact ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice (function_closed_context f))))
    (Classical.choice hc)⟩
end DiophantineConsistency.IPRAFunctionCongruenceClosed
