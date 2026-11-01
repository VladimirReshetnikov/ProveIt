import DiophantineConsistency.IPRADefiningInstances
import DiophantineConsistency.IPRAFunctionCongruenceOpen
set_option autoImplicit false
namespace DiophantineConsistency.IPRAAddOneDirect
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRADefiningInstances IPRAFunctionCongruenceOpen
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def oneArgs : Codes 0 1 := .cons (.zero 0) (.nil 0)
def swapArgs : Codes 2 2 := .cons (.proj 1) (.cons (.proj 0) (.nil 2))
def g : Code 3 := .comp .succ (.cons (.proj 1) (.nil 3))
def compAx {m n : ℕ} (f : Code m) (v : Codes n m) : Propositionᵢ language :=
  Rewriting.emb (compositionEquationI f v)
def projAx {n : ℕ} (i : Fin n) : Propositionᵢ language := Rewriting.emb (projectionEquationI i)
def baseAx : Propositionᵢ language := Rewriting.emb (recursionBaseEquationI (.proj (0 : Fin 1)) g)
def stepAx : Propositionᵢ language := Rewriting.emb (recursionStepEquationI (.proj (0 : Fin 1)) g)
def Γ : List (Propositionᵢ language) := [
  compAx .succ oneArgs, compAx addCore swapArgs, compAx .succ (.cons (.proj 1) (.nil 3)),
  projAx (0 : Fin 1), projAx (0 : Fin 2), projAx (1 : Fin 2), projAx (1 : Fin 3),
  baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx,
  funAx addCore (0 : Fin 2), funAx addCore (1 : Fin 2), funAx .succ (0 : Fin 1)]
def z : SyntacticTerm language := .func (.zero 0) Fin.elim0
def one : SyntacticTerm language := .func oneCode Fin.elim0
def sc (a : SyntacticTerm language) : SyntacticTerm language := .func .succ (fun _ => a)
def core (a b : SyntacticTerm language) : SyntacticTerm language := .func addCore ![a,b]
def add (a b : SyntacticTerm language) : SyntacticTerm language := .func addCode ![a,b]

theorem one_equation : Γ ⊢[𝗜𝗻𝘁¹] equal one (sc z) := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] compAx .succ oneArgs := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := composition_instance .succ oneArgs Fin.elim0 Γ h
  convert hs using 1
  simp [one, sc, z, oneCode, oneArgs, getCode, equal, IPRANativeEquationSpecialize.equal]
theorem trans {a b c : SyntacticTerm language} (h : Γ ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : Γ ⊢[𝗜𝗻𝘁¹] equal b c) : Γ ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context Γ (by simp [Γ]) a b c) h) j

theorem succ_congr {a b : SyntacticTerm language} (h : Γ ⊢[𝗜𝗻𝘁¹] equal a b) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (sc a) (sc b) := by
  have hx : ∀ i : Fin 1, funAx Code.succ i ∈ Γ := by
    intro i; cases i using Fin.cases with
    | zero => simp [Γ]
    | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 1, Γ ⊢[𝗜𝗻𝘁¹] equal ((fun _ : Fin 1 => a) i) ((fun _ : Fin 1 => b) i) := by
    intro i; exact h
  exact function_open_in_context Code.succ Γ (by simp [Γ]) (by simp [Γ]) hx _ _ hr

theorem core_congr {a b c d : SyntacticTerm language}
    (h : Γ ⊢[𝗜𝗻𝘁¹] equal a b) (j : Γ ⊢[𝗜𝗻𝘁¹] equal c d) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (core a c) (core b d) := by
  have hx : ∀ i : Fin 2, funAx addCore i ∈ Γ := by
    intro i; cases i using Fin.cases with
    | zero => simp [Γ]
    | succ i => cases i using Fin.cases with
      | zero => simp [Γ]
      | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 2, Γ ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context addCore Γ (by simp [Γ]) (by simp [Γ]) hx _ _ hr

theorem projection0 (a : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (.func (.proj 0) ![a]) a := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] projAx (0 : Fin 1) := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := projection_instance (0 : Fin 1) ![a] Γ h
  simpa [equal, IPRANativeEquationSpecialize.equal] using hs

theorem projection20 (a b : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (.func (.proj 0) ![a,b]) a := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] projAx (0 : Fin 2) := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := projection_instance (0 : Fin 2) ![a,b] Γ h
  simpa [equal, IPRANativeEquationSpecialize.equal] using hs

theorem projection21 (a b : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (.func (.proj 1) ![a,b]) b := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] projAx (1 : Fin 2) := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := projection_instance (1 : Fin 2) ![a,b] Γ h
  simpa [equal, IPRANativeEquationSpecialize.equal] using hs

theorem projection31 (a b c : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (.func (.proj 1) ![a,b,c]) b := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] projAx (1 : Fin 3) := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := projection_instance (1 : Fin 3) ![a,b,c] Γ h
  simpa [equal, IPRANativeEquationSpecialize.equal] using hs
theorem swap_equation (a b : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (add a b) (core b a) := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] compAx addCore swapArgs := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := composition_instance addCore swapArgs ![a,b] Γ h
  have hc := core_congr (projection21 a b) (projection20 a b)
  apply trans ?_ hc
  convert hs using 1
  simp [add, core, addCode, swapArgs, getCode, equal, IPRANativeEquationSpecialize.equal]
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem core_base (a : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (core z a) a := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] baseAx := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := recursion_base_instance (.proj (0 : Fin 1)) g ![a] Γ h
  apply trans ?_ (projection0 a)
  convert hs using 1
  simp [core, z, addCore, g, equal, IPRANativeEquationSpecialize.equal]
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem g_equation (a b c : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (.func g ![a,b,c]) (sc b) := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] compAx Code.succ (.cons (.proj 1) (.nil 3)) :=
    ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := composition_instance Code.succ (.cons (.proj 1) (.nil 3)) ![a,b,c] Γ h
  apply trans ?_ (succ_congr (projection31 a b c))
  convert hs using 1
  simp [g, sc, getCode, equal, IPRANativeEquationSpecialize.equal]

theorem core_step (a b : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (core (sc a) b) (sc (core a b)) := by
  have h : Γ ⊢[𝗜𝗻𝘁¹] stepAx := ⟨FiniteContext.byAxm (by simp [Γ])⟩
  have hs := recursion_step_instance (.proj (0 : Fin 1)) g ![a,b] Γ h
  apply trans ?_ (g_equation a (core a b) b)
  convert hs using 1
  simp [core, sc, addCore, g, equal, IPRANativeEquationSpecialize.equal]
  constructor
  · funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i
  · funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i

theorem add_one_open (a : SyntacticTerm language) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (add a one) (sc a) := by
  exact trans (swap_equation a one) (trans (core_congr one_equation (refl_context Γ (by simp [Γ]) a))
    (trans (core_step z a) (succ_congr (core_base a))))
def addOneI : Sentenceᵢ language := ∀⁰ (.rel .eq ![stepTerm 0, applyCode .succ (fun _ => #0)])

theorem add_one_closed_context : Γ ⊢[𝗜𝗻𝘁¹] ∀⁰ (.rel .eq ![.func addCode ![#0, .func oneCode Fin.elim0], .func .succ (fun _ => #0)]) := by
  have hΓ : Γ⁺ = Γ := by simp [Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  have ho := Classical.choice (add_one_open (&0))
  convert ho using 1
  simp [add, sc, one, equal, Rewriting.free, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ i => exact Fin.elim0 i
theorem add_one_native : nativeTheory ⊢ addOneI := by
  let Δ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : ∀ p ∈ Γ, Δ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionBase _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionStep _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution IPRAEqualityTransGG.matrix))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCore (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCore (1 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix Code.succ (0 : Fin 1))))
  have hc : Δ *⊢[𝗜𝗻𝘁¹] ⋀Γ := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hax
  have hi := Context.mdp (Context.of (FiniteContext.toDef (Classical.choice add_one_closed_context))) (Classical.choice hc)
  change Δ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb addOneI : Propositionᵢ language)
  apply Nonempty.intro
  convert hi using 1
  simp [addOneI, Rewriting.emb, stepTerm, applyCode, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ i => exact Fin.elim0 i

end DiophantineConsistency.IPRAAddOneDirect
