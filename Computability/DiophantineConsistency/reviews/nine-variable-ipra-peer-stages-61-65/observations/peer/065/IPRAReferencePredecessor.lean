import DiophantineConsistency.IPRAReferenceEqualityTools
import DiophantineConsistency.IPRAErasedSuccessorShape

/-! Exploratory reference-theory instances of the predecessor recursion. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace DiophantineConsistency.IPRAReferencePredecessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
open DiophantineConsistency.IPRAEqualityOnlyReference
open DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRAReferenceEqualityTools
open DiophantineConsistency.PRAFiniteFunctionCodes

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

def succ (x : Term language ℕ) : Term language ℕ := .func .succ (fun _ => x)
def pred (x : Term language ℕ) : Term language ℕ := .func PRATheory.predCode (fun _ => x)
def projection (x y : Term language ℕ) : Term language ℕ := .func (.proj 0) ![x,y]

def stepOpen (x : Term language ℕ) :
    extended referenceTheory ⊢! eqAt (pred (succ x)) (projection x (pred x)) := by
  let params : Fin 0 → TermN 1 := fun i => .bvar i.succ
  let counter : TermN 1 := .bvar 0
  let previous := applyCode (.prec (.zero 0) (.proj 0)) (Fin.cases counter params)
  let body : Semisentenceᵢ language 1 := .rel EqualityRel.eq
    ![applyCode (.prec (.zero 0) (.proj 0)) (Fin.cases (applyCode .succ (fun _ => counter)) params),
      applyCode (.proj 0) (Fin.cases counter (Fin.cases previous params))]
  have ha : referenceTheory ⊢! ∀⁰* body :=
    Axiomatized.prfAxm (ReferenceAxiom.defining (DefiningEquation.recursionStep (.zero 0) (.proj 0)))
  have hp := instantiateTheory (T := referenceTheory) body ha ![x]
  convert hp using 1
  simp only [body, eqAt, Semiformulaᵢ.rew_rel]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [applyCode, pred, succ, PRATheory.predCode, Rew.func, counter, params, Function.comp_def]
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp [applyCode, projection, pred, PRATheory.predCode, Rew.func, counter, params, previous, Function.comp_def]
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) l
      rfl

def projectionOpen (x y : Term language ℕ) :
    extended referenceTheory ⊢! eqAt (projection x y) x := by
  let body : Semisentenceᵢ language 2 := .rel EqualityRel.eq
    ![applyCode (.proj 0) (vars 2), .bvar 0]
  have ha : referenceTheory ⊢! ∀⁰* body :=
    Axiomatized.prfAxm (ReferenceAxiom.defining (DefiningEquation.projection (0 : Fin 2)))
  have hp := instantiateTheory (T := referenceTheory) body ha ![x,y]
  convert hp using 1
  simp only [body, eqAt, Semiformulaᵢ.rew_rel]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [applyCode, projection, vars, Rew.func, Function.comp_def]
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

def predecessorSuccOpen (x : Term language ℕ) :
    extended referenceTheory ⊢! eqAt (pred (succ x)) x := by
  let φ : Semisentenceᵢ language 2 := .rel EqualityRel.eq ![#1,#0]
  have ht := replaceParameter φ (projection x (pred x)) x ![pred (succ x)]
  have ht' : extended referenceTheory ⊢!
      eqAt (projection x (pred x)) x 🡒
        (eqAt (pred (succ x)) (projection x (pred x)) 🡒 eqAt (pred (succ x)) x) := by
    (convert ht using 1) <;>
      simp [φ, eqAt, Semiformulaᵢ.rew_rel]
    constructor
    all_goals funext i; refine Fin.cases ?_ (fun j => ?_) i
    all_goals first | rfl | (refine Fin.cases ?_ (fun k => Fin.elim0 k) j; rfl)
  exact ht' ⨀ projectionOpen x (pred x) ⨀ stepOpen x

def injectivityOpen (x y : Term language ℕ) :
    extended referenceTheory ⊢! eqAt (succ x) (succ y) 🡒 eqAt x y := by
  let φ : Semisentenceᵢ language 2 := .rel EqualityRel.eq
    ![.func PRATheory.predCode (fun _ => #0), #1]
  have ht := replaceParameter φ (succ x) (succ y) ![x]
  have ht' : extended referenceTheory ⊢!
      eqAt (succ x) (succ y) 🡒 (eqAt (pred (succ x)) x 🡒 eqAt (pred (succ y)) x) := by
    convert ht using 1 <;> simp [φ, eqAt, pred, Semiformulaᵢ.rew_rel]
    constructor <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  let ψ : Semisentenceᵢ language 2 := .rel EqualityRel.eq ![#0,#1]
  have hs := replaceParameter ψ (pred (succ y)) x ![y]
  have hs' : extended referenceTheory ⊢!
      eqAt (pred (succ y)) x 🡒 (eqAt (pred (succ y)) y 🡒 eqAt x y) := by
    convert hs using 1 <;> simp [ψ, eqAt, Semiformulaᵢ.rew_rel]
    constructor <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have hh : [eqAt (succ x) (succ y)] ⊢[extended referenceTheory]! eqAt x y := by
    have hxy : [eqAt (succ x) (succ y)] ⊢[extended referenceTheory]! eqAt (succ x) (succ y) :=
      Entailment.FiniteContext.byAxm₀
    exact (Entailment.FiniteContext.of hs') ⨀
      ((Entailment.FiniteContext.of ht') ⨀ hxy ⨀ (Entailment.FiniteContext.of (predecessorSuccOpen x))) ⨀
      (Entailment.FiniteContext.of (predecessorSuccOpen y))
  have h := Entailment.FiniteContext.deduct! ⟨hh⟩
  have ht := Entailment.FiniteContext.toDef (Classical.choice h)
  simpa using (ht ⨀ (Entailment.verum : extended referenceTheory ⊢! ⊤))

def successorInjectivityImage : referenceTheory ⊢! IPRAOrderErasure.erase IPRANativeTheory.succInjectiveI := by
  rw [IPRAErasedSuccessorShape.erase_successorInjectivity]
  unfold IPRAErasedSuccessorShape.injectivity
  apply IPRAReferenceCloseFamily.closeFamily referenceTheory 2
  intro v
  have h := injectivityOpen (v 0) (v 1)
  convert h using 1
  simp [eqAt, succ, IPRAEqualityOnlyReference.applyCode, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j

end DiophantineConsistency.IPRAReferencePredecessor
