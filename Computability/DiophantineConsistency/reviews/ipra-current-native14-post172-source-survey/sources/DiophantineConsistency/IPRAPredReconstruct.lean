import DiophantineConsistency.IPRAAddOneDirect
import DiophantineConsistency.IPRAZeroDecidable
import DiophantineConsistency.IPRAEqualitySymmetryGG
set_option autoImplicit false
namespace DiophantineConsistency.IPRAPredReconstruct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRADefiningInstances
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def predStepAx : Propositionᵢ language := Rewriting.emb (recursionStepEquationI (.zero 0) (.proj (0 : Fin 2)))
def Δ : List (Propositionᵢ language) := [predStepAx, funAx predCode (0 : Fin 1), Rewriting.emb IPRAEqualitySymmetryGG.symmI] ++ Γ
def pred (a : SyntacticTerm language) : SyntacticTerm language := .func predCode (fun _ => a)
theorem lift_old {φ : Propositionᵢ language} (h : Γ ⊢[𝗜𝗻𝘁¹] φ) : Δ ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro p hp; simp [Δ, hp]) (Classical.choice h)⟩
theorem refl_new (a : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal a a :=
  refl_context Δ (by simp [Δ, Γ]) a
theorem trans_new {a b c : SyntacticTerm language} (h : Δ ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : Δ ⊢[𝗜𝗻𝘁¹] equal b c) : Δ ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context Δ (by simp [Δ, Γ]) a b c) h) j
theorem congr_succ {a b : SyntacticTerm language} (h : Δ ⊢[𝗜𝗻𝘁¹] equal a b) : Δ ⊢[𝗜𝗻𝘁¹] equal (sc a) (sc b) := by
  have hx : ∀ i : Fin 1, funAx Code.succ i ∈ Δ := by
    intro i; cases i using Fin.cases with
    | zero => simp [Δ, Γ]
    | succ i => exact Fin.elim0 i
  exact function_open_in_context Code.succ Δ (by simp [Δ, Γ]) (by simp [Δ, Γ]) hx _ _ (fun _ => h)
theorem congr_pred {a b : SyntacticTerm language} (h : Δ ⊢[𝗜𝗻𝘁¹] equal a b) : Δ ⊢[𝗜𝗻𝘁¹] equal (pred a) (pred b) := by
  have hx : ∀ i : Fin 1, funAx predCode i ∈ Δ := by
    intro i; cases i using Fin.cases with
    | zero => simp [Δ]
    | succ i => exact Fin.elim0 i
  exact function_open_in_context predCode Δ (by simp [Δ, Γ]) (by simp [Δ, Γ]) hx _ _ (fun _ => h)
theorem pred_succ (a : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal (pred (sc a)) a := by
  have h : Δ ⊢[𝗜𝗻𝘁¹] predStepAx := ⟨FiniteContext.byAxm (by simp [Δ])⟩
  have hs := recursion_step_instance (.zero 0) (.proj (0 : Fin 2)) ![a] Δ h
  apply trans_new ?_ (lift_old (projection20 a (pred a)))
  convert hs using 1
  simp [pred, sc, predCode, equal, IPRANativeEquationSpecialize.equal]
  funext i; cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero =>
      simp only [Fin.cases_succ, Matrix.cons_val_succ, Matrix.cons_val_zero]
      congr 1
      funext j; cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
    | succ i => exact Fin.elim0 i
theorem symm_new (a b : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal a b 🡒 equal b a := by
  have hc : Δ ⊢[𝗜𝗻𝘁¹] Rewriting.emb IPRAEqualitySymmetryGG.symmI :=
    ⟨FiniteContext.byAxm (by simp [Δ])⟩
  let p : Semiformulaᵢ language ℕ 2 := Rewriting.emb ((Semiformulaᵢ.rel .eq ![#1,#0] 🡒 Semiformulaᵢ.rel .eq ![#0,#1]) : Semisentenceᵢ language 2)
  have hp : Δ ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    let q : Semisentenceᵢ language 2 := .rel .eq ![#1,#0] 🡒 .rel .eq ![#0,#1]
    have hq : Δ ⊢[𝗜𝗻𝘁¹] Rewriting.emb (∀⁰* q) := by
      simpa [q, IPRAEqualitySymmetryGG.symmI, allClosure_succ] using hc
    simpa only [p, q, Rewriting.emb_allClosure] using hq
  have hs := IPRAAllSpecialize.specialize_over_context p ![b,a] Δ hp
  convert hs using 1
  simp [p, equal, Rewriting.subst, Rewriting.emb, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem reconstruct_step (a : SyntacticTerm language) :
    Δ ⊢[𝗜𝗻𝘁¹] equal (add a one) (sc (pred (add a one))) := by
  have hone := lift_old (add_one_open a)
  have hp : Δ ⊢[𝗜𝗻𝘁¹] equal (pred (add a one)) a :=
    trans_new (congr_pred hone) (pred_succ a)
  exact trans_new hone (Entailment.mdp! (symm_new _ _) (congr_succ hp))
def reconEq : Semisentenceᵢ language 1 := .rel .eq ![#0, .func .succ (fun _ => .func predCode (fun _ => #0))]
def reconstruct : Semisentenceᵢ language 1 := IPRAZeroDecidable.zeroEq ⋎ reconEq

theorem reconstruct_open : IPRAQuantifierFree.OpenI reconstruct := by
  simp [reconstruct, IPRAZeroDecidable.zeroEq, reconEq, IPRAQuantifierFree.OpenI]

theorem step_closed_context : Δ ⊢[𝗜𝗻𝘁¹] ∀⁰ Rewriting.emb (atStep reconEq) := by
  have hΔ : Δ⁺ = Δ := by
    simp [Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΔ]
  have ho := Classical.choice (reconstruct_step (&0))
  convert ho using 1
  simp [atStep, reconEq, stepTerm, Semiformulaᵢ.rew_rel, Rewriting.free, equal, add, one, sc, pred]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      funext k; congr 1; funext l; congr 1
      funext j; cases j using Fin.cases with
      | zero => rfl
      | succ j => cases j using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
        | succ j => exact Fin.elim0 j
    | succ i => exact Fin.elim0 i
theorem step_native : nativeTheory ⊢ ∀⁰ atStep reconEq := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : ∀ p ∈ Γ, Θ *⊢[𝗜𝗻𝘁¹] p := by
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
  have hδ : ∀ p ∈ Δ, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [Δ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl | rfl) | hp
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionStep _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality
        (EqualityAxiomI.substitution (funMatrix predCode (0 : Fin 1))))
    · exact IPRAEqualitySymmetryGG.symmetry_native
    · exact hax p hp
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀Δ := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hδ
  have hi := Context.mdp (Context.of (FiniteContext.toDef (Classical.choice step_closed_context))) (Classical.choice hc)
  change Θ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb (∀⁰ atStep reconEq) : Propositionᵢ language)
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]
theorem recon_base : nativeTheory ⊢ atZero reconstruct := by
  have hr : nativeTheory ⊢ eqReflI := IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
  have hs : nativeTheory ⊢ atZero IPRAZeroDecidable.zeroEq := by
    have hs' := IPRAAllSpecialize.allClosure_specialize (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) 1
      (Rewriting.emb (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#0] : Semisentenceᵢ language 1))
      (fun _ => (.func (PRAFiniteFunctionCodes.Code.zero 0) Fin.elim0 : SyntacticTerm language))
    have hs'' := Classical.choice hs'
    have h := Entailment.mdp! (show nativeTheory ⊢ eqReflI 🡒 atZero IPRAZeroDecidable.zeroEq by
      apply Nonempty.intro
      apply Theoryᵢ.ofHilbert
      convert hs'' using 1
      simp [eqReflI, atZero, IPRAZeroDecidable.zeroEq, zeroTerm, Rewriting.subst, Semiformulaᵢ.rew_rel]
      funext i
      cases i using Fin.cases with
      | zero =>
        simp [Rew.func, Function.comp_def]
        funext i
        exact Fin.elim0 i
      | succ j =>
        cases j using Fin.cases with
        | zero =>
          simp [Rew.func, Function.comp_def]
          funext i
          exact Fin.elim0 i
        | succ j => exact Fin.elim0 j) hr
    exact h
  have ho : nativeTheory ⊢ atZero IPRAZeroDecidable.zeroEq 🡒 atZero reconstruct := by
    apply Nonempty.intro
    apply Theoryᵢ.ofHilbert
    simpa [atZero, reconstruct] using (Entailment.or₁ (𝓢 := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
      (φ := Rewriting.emb (atZero IPRAZeroDecidable.zeroEq)) (ψ := Rewriting.emb (atZero reconEq)))
  exact Entailment.mdp! ho hs

theorem all_step_of_right {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
    (p q r : Semipropositionᵢ L 1) : Λ ⊢ (∀⁰ q) 🡒 ∀⁰ (p 🡒 (r ⋎ q)) := by
  have hp : Λ ⊢! (Rewriting.free q) 🡒
      (Rewriting.free p 🡒 (Rewriting.free r ⋎ Rewriting.free q)) :=
    Entailment.C_trans Entailment.or₂ Entailment.implyK
  have hg : Λ ⊢! Rewriting.free (q 🡒 (p 🡒 (r ⋎ q))) := by simpa using hp
  exact ⟨HilbertProofᵢ.allImplyAllOfAllImply _ _ ⨀ HilbertProofᵢ.gen hg⟩

theorem recon_step_native : nativeTheory ⊢ ∀⁰ (reconstruct 🡒 atStep reconstruct) := by
  have hl := all_step_of_right (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (Rewriting.emb reconstruct) (Rewriting.emb (atStep reconEq))
    (Rewriting.emb (atStep IPRAZeroDecidable.zeroEq))
  have htheory : nativeTheory ⊢ (∀⁰ atStep reconEq) 🡒 ∀⁰ (reconstruct 🡒 atStep reconstruct) := by
    apply Nonempty.intro
    apply Theoryᵢ.ofHilbert
    have hh := Classical.choice hl
    convert hh using 1
    simp [reconstruct, atStep]
  exact Entailment.mdp! htheory step_native

theorem reconstruction : nativeTheory ⊢ ∀⁰ reconstruct := by
  have h : nativeTheory ⊢ inductionAxiom reconstruct :=
    IPRANativeAxiomImage.native_axiom (NativeAxiom.induction ⟨0, reconstruct, reconstruct_open, rfl⟩)
  exact Entailment.mdp! (Entailment.mdp! h recon_base) recon_step_native

end DiophantineConsistency.IPRAPredReconstruct
