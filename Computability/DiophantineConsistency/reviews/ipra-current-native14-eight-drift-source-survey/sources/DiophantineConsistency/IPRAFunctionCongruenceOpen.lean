import DiophantineConsistency.IPRAAllSpecialize
import DiophantineConsistency.IPRAEqualityTransGG
/-! Arbitrary-arity open function congruence from native Leibniz,
reflexivity and transitivity. The source closed GG image remains separate. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAFunctionCongruenceOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory IPRAAllSpecialize

def funMatrix {k : ℕ} (f : language.Func k) (i : Fin k) : Semisentenceᵢ language (k+1) :=
  Semiformulaᵢ.rel .eq ![
    Semiterm.func f (fun j => #j.succ),
    Semiterm.func f (fun j => if j = i then #0 else #j.succ)]

def vec {k : ℕ} (x y : SyntacticTerm language)
    (v : Fin k → SyntacticTerm language) : Fin (k+2) → SyntacticTerm language :=
  Fin.cases x (Fin.cases y v)

def update {k : ℕ} (i : Fin k) (x : SyntacticTerm language)
    (v : Fin k → SyntacticTerm language) : Fin k → SyntacticTerm language :=
  fun j => if j = i then x else v j

def equal {n : ℕ} (x y : Semiterm language ℕ n) : Semiformulaᵢ language ℕ n := Semiformulaᵢ.rel .eq ![x,y]

theorem function_matrix_specialized {k : ℕ} (f : language.Func k) (i : Fin k)
    (x y : SyntacticTerm language) (v : Fin k → SyntacticTerm language) :
    (Rewriting.emb (leibnizBody (funMatrix f i)) : Semiformulaᵢ language ℕ (k+2)) ⇜ vec x y v =
      (equal x y 🡒 equal (Semiterm.func f v) (Semiterm.func f (update i x v)) 🡒
        equal (Semiterm.func f v) (Semiterm.func f (update i y v))) := by
  simp [leibnizBody, eqLeft, eqRight, funMatrix, Rewriting.subst,
    Semiformulaᵢ.rew_rel, equal]
  refine ⟨?_, ?_, ?_⟩ <;> funext j <;> cases j using Fin.cases with
  | zero =>
    simp [vec, Rew.func] <;> funext z <;> rfl
  | succ j => cases j using Fin.cases with
    | zero =>
      first | rfl | (simp [Rew.func]; funext z; by_cases h : z = i <;> simp [update, vec, h] <;> rfl)
    | succ j => exact Fin.elim0 j
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem update_self {k : ℕ} (i : Fin k) (v : Fin k → SyntacticTerm language) :
    update i (v i) v = v := by
  funext j
  by_cases h : j = i <;> simp [update, h]

def funAx {k : ℕ} (f : language.Func k) (i : Fin k) : Propositionᵢ language :=
  Rewriting.emb (eqSubstitutionI (funMatrix f i))
def reflAx : Propositionᵢ language := Rewriting.emb eqReflI

theorem one_coordinate_open {k : ℕ} (f : language.Func k) (i : Fin k)
    (y : SyntacticTerm language) (v : Fin k → SyntacticTerm language) :
    [funAx f i, reflAx] ⊢[𝗜𝗻𝘁¹]
      equal (v i) y 🡒 equal (Semiterm.func f v) (Semiterm.func f (update i y v)) := by
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [equal (v i) y, funAx f i, reflAx]
  have he : Γ ⊢[𝗜𝗻𝘁¹]! equal (v i) y := FiniteContext.byAxm₀
  have ha : Γ ⊢[𝗜𝗻𝘁¹] funAx f i := ⟨FiniteContext.byAxm₁⟩
  have hr : Γ ⊢[𝗜𝗻𝘁¹] reflAx := ⟨FiniteContext.byAxm₂⟩
  have ht := specialize_native_leibniz (funMatrix f i) (vec (v i) y v) Γ ha
  rw [function_matrix_specialized, update_self] at ht
  let p : Semiformulaᵢ language ℕ 1 := Semiformulaᵢ.rel .eq ![#0,#0]
  have hr' : Γ ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    convert hr using 1
    simp [reflAx, eqReflI, p, Semiformulaᵢ.rew_rel]
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have h := specialize_over_context p ![Semiterm.func f v] Γ hr'
  have hh : Γ ⊢[𝗜𝗻𝘁¹] equal (Semiterm.func f v) (Semiterm.func f v) := by
    convert h using 1
    simp [p, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  exact ⟨(Classical.choice ht ⨀ he) ⨀ Classical.choice hh⟩
theorem trans_context (Γ : List (Propositionᵢ language))
    (hax : IPRAEqualityTransGG.ax ∈ Γ) (a b c : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal a b 🡒 equal b c 🡒 equal a c := by
  let p : Semiformulaᵢ language ℕ 3 := equal #2 #1 🡒 equal #1 #0 🡒 equal #2 #0
  have hclosed : Γ ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    apply Nonempty.intro
    apply FiniteContext.weakening (Γ := [IPRAEqualityTransGG.ax])
    · simpa using hax
    · exact Classical.choice IPRAEqualityTransGG.trans_closed_context
  have ht := specialize_over_context p ![c,b,a] Γ hclosed
  convert ht using 1
  simp [p, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  refine ⟨?_, ?_, ?_⟩ <;> funext j <;> cases j using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
theorem refl_context (Γ : List (Propositionᵢ language))
    (hax : reflAx ∈ Γ) (a : SyntacticTerm language) : Γ ⊢[𝗜𝗻𝘁¹] equal a a := by
  have hr : Γ ⊢[𝗜𝗻𝘁¹] reflAx := ⟨FiniteContext.byAxm hax⟩
  let p : Semiformulaᵢ language ℕ 1 := Semiformulaᵢ.rel .eq ![#0,#0]
  have hr' : Γ ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    convert hr using 1
    simp [reflAx, eqReflI, p, Semiformulaᵢ.rew_rel]
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have h := specialize_over_context p ![a] Γ hr'
  convert h using 1
  simp [p, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
def mix {k : ℕ} (s : Finset (Fin k)) (v w : Fin k → SyntacticTerm language) :
    Fin k → SyntacticTerm language := fun j => if j ∈ s then w j else v j

theorem mix_insert {k : ℕ} (s : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → SyntacticTerm language) :
    mix (insert i s) v w = update i (w i) (mix s v w) := by
  funext j
  by_cases h : j = i
  · subst j; simp [mix, update]
  · simp [mix, update, h]

def functionContext {k : ℕ} (f : language.Func k) : List (Propositionᵢ language) :=
  [IPRAEqualityTransGG.ax, reflAx] ++ List.ofFn (fun i : Fin k => funAx f i)

theorem function_open_in_context {k : ℕ} (f : language.Func k)
    (Γ : List (Propositionᵢ language))
    (href : reflAx ∈ Γ) (htrans : IPRAEqualityTransGG.ax ∈ Γ)
    (hfun : ∀ i, funAx f i ∈ Γ)
    (v w : Fin k → SyntacticTerm language)
    (h : ∀ i, Γ ⊢[𝗜𝗻𝘁¹] equal (v i) (w i)) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (Semiterm.func f v) (Semiterm.func f w) := by
  have hempty : mix ∅ v w = v := by funext i; simp [mix]
  have huniv : mix Finset.univ v w = w := by funext i; simp [mix]
  have hm : ∀ s : Finset (Fin k), Γ ⊢[𝗜𝗻𝘁¹]
      equal (Semiterm.func f v) (Semiterm.func f (mix s v w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [hempty] using refl_context Γ href (Semiterm.func f v)
    | @insert i s hi ih =>
      have he : Γ ⊢[𝗜𝗻𝘁¹] equal ((mix s v w) i) (w i) := by
        simpa [mix, hi] using h i
      have hs : Γ ⊢[𝗜𝗻𝘁¹]
          equal (Semiterm.func f (mix s v w))
            (Semiterm.func f (update i (w i) (mix s v w))) := by
        have ho := one_coordinate_open f i (w i) (mix s v w)
        have ho' : Γ ⊢[𝗜𝗻𝘁¹] equal ((mix s v w) i) (w i) 🡒
            equal (Semiterm.func f (mix s v w))
              (Semiterm.func f (update i (w i) (mix s v w))) := by
          apply Nonempty.intro
          apply FiniteContext.weakening (Γ := [funAx f i, reflAx])
          · simpa using And.intro (hfun i) href
          · exact Classical.choice ho
        exact Entailment.mdp! ho' he
      have ht := trans_context Γ htrans (Semiterm.func f v)
        (Semiterm.func f (mix s v w))
        (Semiterm.func f (update i (w i) (mix s v w)))
      have hh := Entailment.mdp! (Entailment.mdp! ht ih) hs
      simpa only [mix_insert] using hh
  simpa only [huniv] using hm Finset.univ
theorem function_open {k : ℕ} (f : language.Func k)
    (v w : Fin k → SyntacticTerm language)
    (h : ∀ i, functionContext f ⊢[𝗜𝗻𝘁¹] equal (v i) (w i)) :
    functionContext f ⊢[𝗜𝗻𝘁¹] equal (Semiterm.func f v) (Semiterm.func f w) := by
  apply function_open_in_context f (functionContext f)
  · simp [functionContext]
  · simp [functionContext]
  · intro i; simp [functionContext]
  · exact h
theorem matrix_conj_elim (n : ℕ) (v : Fin n → Propositionᵢ language) (i : Fin n) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢ Matrix.conj v 🡒 v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact ⟨Entailment.and₁⟩
    | succ i =>
      exact ⟨Entailment.C_trans Entailment.and₂ (Classical.choice (ih (Matrix.vecTail v) i))⟩
theorem function_conj_open {k : ℕ} (f : language.Func k)
    (v w : Fin k → SyntacticTerm language) :
    functionContext f ⊢[𝗜𝗻𝘁¹]
      (Matrix.conj fun i => equal (v i) (w i)) 🡒
        equal (Semiterm.func f v) (Semiterm.func f w) := by
  apply FiniteContext.deduct!
  let A := Matrix.conj fun i => equal (v i) (w i)
  let Γ := A :: functionContext f
  have href : reflAx ∈ Γ := by simp [Γ, functionContext]
  have htrans : IPRAEqualityTransGG.ax ∈ Γ := by simp [Γ, functionContext]
  have hfun (i : Fin k) : funAx f i ∈ Γ := by simp [Γ, functionContext]
  have heq (i : Fin k) : Γ ⊢[𝗜𝗻𝘁¹] equal (v i) (w i) := by
    have hA : Γ ⊢[𝗜𝗻𝘁¹]! A := FiniteContext.byAxm₀
    have hp := Classical.choice (matrix_conj_elim k (fun i => equal (v i) (w i)) i)
    exact ⟨FiniteContext.of hp ⨀ hA⟩
  exact function_open_in_context f Γ href htrans hfun v w heq
theorem functionContext_shift {k : ℕ} (f : language.Func k) :
    (functionContext f)⁺ = functionContext f := by
  simp [functionContext, IPRAEqualityTransGG.ax, reflAx, funAx, Rewriting.shifts,
    Rewriting.rew_emb_eq_emb]
  funext i
  exact Rewriting.rew_emb_eq_emb _ _

theorem allClosure_fixitr_context (Γ : List (Propositionᵢ language))
    (hΓ : Γ⁺ = Γ) {p : Propositionᵢ language} (h : Γ ⊢[𝗜𝗻𝘁¹] p) :
    ∀ m, Γ ⊢[𝗜𝗻𝘁¹] ∀⁰* (Rew.fixitr 0 m ▹ p)
  | 0 => by simpa using h
  | m+1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    apply Nonempty.intro
    apply HilbertProofᵢ.geNOverFiniteContext
    rw [hΓ]
    simpa using Classical.choice (allClosure_fixitr_context Γ hΓ h m)
theorem rew_matrix_conj {ξ₁ ξ₂ : Type} {n₁ n₂ k : ℕ}
    (ω : Rew language ξ₁ n₁ ξ₂ n₂) (v : Fin k → Semiformulaᵢ language ξ₁ n₁) :
    ω ▹ Matrix.conj v = Matrix.conj (fun i => ω ▹ v i) := by
  induction k with
  | zero => simp [Matrix.conj]
  | succ k ih => simp [Matrix.conj, Matrix.vecTail, Function.comp_def, ih]
end DiophantineConsistency.IPRAFunctionCongruenceOpen
