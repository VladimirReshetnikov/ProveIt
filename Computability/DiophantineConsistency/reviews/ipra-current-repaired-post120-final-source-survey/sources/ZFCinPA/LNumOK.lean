import ZFCinPA.LDriverBase
import ZFCinPA.LTransVal

set_option autoImplicit false
noncomputable section

/-!
# Numeral chains define natural numbers, provably in `𝗭𝗙`

The atomic steps of the reflection generator read environment slots through
the von Neumann numeral chains `NumeralOmega.numChainQ x`, and their
templates assume `numOK₀`/`numOK₂`: the numeral placeholder defines exactly
one set, and that set is a natural number. This module proves the
translation `NumOKT (numChainQ x)` in `𝗭𝗙` for **every** internal `x`,
standard or not, by a `Σ₁` induction in the ambient model:

* `numBaseTemplate`: a predicate equivalent to "empty" defines one natural;
* `numStepTemplate`: if `P₀` defines one natural `m` and `P₂ n` is
  `∃ m (P₀ m ∧ n = m ∪ {m})` — literally the shape of `numChainQ_succ` —
  then `P₂` defines one natural.

Both definitional hypotheses translate to tautologies at the chain's own
codes (`numChainQ_zero`, `numChainQ_succ`).
-/

namespace LeanProofs.ZFCinPA.LNumOK

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepAtom
open LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.NumeralOmega (numZeroS succRelS numChainQ numChainQ_zero numChainQ_succ)

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## The templates -/

/-- `P₀` is "empty". -/
def numZeroDef : Sentence L6 := ∀⁰ (P₀ 🡘 lift numZeroS)

/-- `∃ m (P₀ m ∧ succ m = #0)`, literally the shape of `numChainQ_succ`. -/
def numSuccBody : Semisentence L6 1 := ∃⁰ ((P₀ ⇜ ![#0]) ⋏ lift succRelS)

/-- `P₂` is the successor numeral of `P₀`. -/
def numSuccDef : Sentence L6 := ∀⁰ (P₂ 🡘 numSuccBody)

def numBaseTemplate : Sentence L6 := numZeroDef 🡒 numOK₀

def numStepTemplate : Sentence L6 := (numOK₀ ⋏ numSuccDef) 🡒 numOK₂

section Readings

variable {V : Type*} [SetStructure V]

theorem eval_numZeroS (n : V) (ε : Empty → V) :
    numZeroS.Eval (s := SetTheory.standardStructure V) ![n] ε ↔ ∀ w, w ∉ n := by
  simp [numZeroS]

theorem eval_succRelS (m n : V) (ε : Empty → V) :
    succRelS.Eval (s := SetTheory.standardStructure V) ![m, n] ε ↔
      ∀ w, w ∈ n ↔ w ∈ m ∨ w = m := by
  simp only [succRelS]
  simp
  refine forall_congr' fun w => ?_
  tauto

end Readings

theorem numBaseTemplate_provable : templTheory 6 ar6 ⊢ numBaseTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  simp only [numBaseTemplate, Semantics.Imp.models_imply]
  intro hdef
  simp only [models_iff, numZeroDef] at hdef
  simp [eval_numZeroS] at hdef
  simp only [models_iff, numOK₀]
  simp [eval_natP H]
  refine ⟨⟨_root_.SetTheory.vempty H, (hdef _).2 fun w => _root_.SetTheory.vempty_spec H w,
    fun m' hm' => (LClosure.empty_iff m').1 ((hdef m').1 hm')⟩, fun m hm => ?_⟩
  rw [(LClosure.empty_iff m).1 ((hdef m).1 hm)]
  exact _root_.SetTheory.vempty_in_omega H

theorem numStepTemplate_provable : templTheory 6 ar6 ⊢ numStepTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  simp only [numStepTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hok, hdef⟩
  simp only [models_iff, numOK₀] at hok
  simp [eval_natP H] at hok
  obtain ⟨⟨m₀, hm₀, hu⟩, hω⟩ := hok
  simp only [models_iff, numSuccDef, numSuccBody] at hdef
  simp [eval_succRelS] at hdef
  simp only [models_iff, numOK₂]
  simp [eval_natP H]
  have hsucc : ∀ n : M, (∀ w, w ∈ n ↔ w ∈ m₀ ∨ w = m₀) ↔ n = _root_.SetTheory.vsucc H m₀ :=
    fun n => ⟨fun h => _root_.SetTheory.ZFAxioms.ext H _ _ fun w =>
        (h w).trans (_root_.SetTheory.vsucc_spec H m₀ w).symm,
      fun h w => h ▸ _root_.SetTheory.vsucc_spec H m₀ w⟩
  have hP₂ : ∀ n : M, P₂.Eval ![n] Empty.elim ↔ n = _root_.SetTheory.vsucc H m₀ := by
    intro n
    rw [hdef n]
    constructor
    · rintro ⟨m, hm, hmn⟩
      rw [hu m hm] at hmn
      exact (hsucc n).1 hmn
    · intro hn
      exact ⟨m₀, hm₀, (hsucc n).2 hn⟩
  refine ⟨⟨_, (hP₂ _).2 rfl, fun m' hm' => (hP₂ m').1 hm'⟩, fun m hm => ?_⟩
  rw [(hP₂ m).1 hm]
  exact _root_.SetTheory.omega_succ H m₀ (hω m₀ hm₀)

/-! ## The internal induction -/

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem tr_numBase (N : SF V 1) :
    translateFormula (K6 N ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb numBaseTemplate) =
      ((∀⁰ (N 🡘 ⌜numZeroS⌝)) 🡒 NumOKT N) := by
  rw [numBaseTemplate, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_numOK₀]
  congr 1
  simp [numZeroDef, P₀, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  rfl

theorem tr_numStep (N₀ N₂ : SF V 1) :
    translateFormula (K6 N₀ ⊤ N₂ ⊤ ⊤ ⊤) (Rewriting.emb numStepTemplate) =
      ((NumOKT N₀ ⋏ (∀⁰ (N₂ 🡘 (∃⁰ (N₀.subst
          (![Bootstrapping.Semiterm.bvar 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 2) ⋏
            ⌜succRelS⌝))))) 🡒 NumOKT N₂) := by
  rw [numStepTemplate, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_numOK₂]
  congr 1
  show translateFormula _ (Rewriting.emb numOK₀) ⋏ translateFormula _ (Rewriting.emb numSuccDef) = _
  rw [tr_numOK₀]
  congr 1
  simp [numSuccDef, numSuccBody, P₀, P₂, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  and_intros <;> rfl


theorem numOK_zero : (𝗭𝗙 : SetTheory).internalize V ⊢ NumOKT (numChainQ (0 : V)) := by
  have h := compileT_provable (V := V) (by decide) (K6 (numChainQ 0) ⊤ ⊤ ⊤ ⊤ ⊤)
    numBaseTemplate_provable
  rw [tr_numBase, numChainQ_zero] at h
  rw [numChainQ_zero]
  exact h ⨀ all_iff_self _

theorem numOK_succ (x : V) (hx : (𝗭𝗙 : SetTheory).internalize V ⊢ NumOKT (numChainQ x)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ NumOKT (numChainQ (x + 1)) := by
  have h := compileT_provable (V := V) (by decide)
    (K6 (numChainQ x) ⊤ (numChainQ (x + 1)) ⊤ ⊤ ⊤) numStepTemplate_provable
  rw [tr_numStep] at h
  refine h ⨀ Entailment.K!_intro hx ?_
  rw [← numChainQ_succ]
  exact all_iff_self _

/-- The code of `NumOKT (numChainQ x)` is `Σ₁` in `x`. -/
theorem numOK_definable :
    𝚺₁.DefinableFunction (fun x : Fin 1 → V ↦ (NumOKT (numChainQ (x 0))).val) := by
  have h := LTransVal.transVal_definable (V := V) (k := 6) (arities := ar6)
    (Rewriting.emb numOK₀ : Semiproposition L6 0)
  have h' := HierarchySymbol.DefinableFunction.substitution (F := fun vals : Fin 6 → V ↦
      LTransVal.transVal vals (Rewriting.emb numOK₀ : Semiproposition L6 0))
    (f := fun i (x : Fin 1 → V) ↦ (K6 (numChainQ (x 0)) ⊤ ⊤ ⊤ ⊤ ⊤ i).val) h (fun i => by
      match i with
      | ⟨0, _⟩ =>
          show 𝚺₁.DefinableFunction fun x : Fin 1 → V ↦ numChainCode (x 0)
          exact HierarchySymbol.DefinableFunction₁.comp (F := numChainCode)
            (HierarchySymbol.DefinableFunction.var 0)
      | ⟨1, _⟩ => exact HierarchySymbol.DefinableFunction.const _
      | ⟨2, _⟩ => exact HierarchySymbol.DefinableFunction.const _
      | ⟨3, _⟩ => exact HierarchySymbol.DefinableFunction.const _
      | ⟨4, _⟩ => exact HierarchySymbol.DefinableFunction.const _
      | ⟨5, _⟩ => exact HierarchySymbol.DefinableFunction.const _)
  exact HierarchySymbol.DefinableFunction.of_eq _
    (fun x ↦ (LTransVal.val_translateFormula _ _).symm) h'

/-- **Every numeral chain defines exactly one natural number, provably in
`𝗭𝗙`**, at every element of the ambient model. -/
theorem numOK (x : V) : (𝗭𝗙 : SetTheory).internalize V ⊢ NumOKT (numChainQ x) := by
  suffices Provable (𝗭𝗙 : SetTheory) (NumOKT (numChainQ x)).val from
    Bootstrapping.tprovable_iff_provable.mpr this
  induction x using ISigma1.sigma1_succ_induction
  · exact HierarchySymbol.DefinablePred.comp (P := Provable (𝗭𝗙 : SetTheory))
      (by definability) numOK_definable
  case zero => exact Bootstrapping.tprovable_iff_provable.mp numOK_zero
  case succ x ih =>
    exact Bootstrapping.tprovable_iff_provable.mp
      (numOK_succ x (Bootstrapping.tprovable_iff_provable.mpr ih))

end LeanProofs.ZFCinPA.LNumOK
