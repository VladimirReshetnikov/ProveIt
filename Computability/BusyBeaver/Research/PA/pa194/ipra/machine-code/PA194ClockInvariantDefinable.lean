import PA194CumulativeClock
import PA194ConditionalModelLength
import PA194CodeGraph
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ClockInvariantDefinable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194CumulativeClock PA194Stepper
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unaryCodeDef (c : Code 1) : 𝚺₁-Function₁ (fun s : M => F c ![s]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F c e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) c)
  convert h using 1
  funext e
  change F c ![e 0] = F c e
  apply congrArg (fun e : Fin 1 → M => F c e)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem binaryCodeDef (c : Code 2) : 𝚺₁-Function₂ (fun s t : M => F c ![s,t]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F c e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) c)
  convert h using 1
  funext e
  exact congrArg (fun e : Fin 2 → M => F c e) (Matrix.fun_eq_vec_two e).symm

theorem bindBinary (f : M → M → M) (seed : M) (hf : 𝚺₁-Function₂ f) :
    𝚺₁-Function₁ (fun n => f n seed) := by
  haveI := hf
  definability

theorem composeUnary (f g : M → M) (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Function₁ (fun n => f (g n)) := by
  haveI := hf
  haveI := hg
  definability

theorem composePred (p : M → Prop) (f : M → M)
    (hp : 𝚺₁-Predicate p) (hf : 𝚺₁-Function₁ f) :
    𝚺₁-Predicate (fun n => p (f n)) := by
  haveI := hp
  haveI := hf
  definability

theorem equalPred (f g : M → M) (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun n => f n = g n) := by
  haveI := hf
  haveI := hg
  definability

theorem andPred (p q : M → Prop) (hp : 𝚺₁-Predicate p) (hq : 𝚺₁-Predicate q) :
    𝚺₁-Predicate (fun n => p n ∧ q n) := by
  haveI := hp
  haveI := hq
  definability

theorem invariantDef (run : Code 2) (cost frame : Code 1) (seed start : M)
    (good : M → Prop) (hgood : 𝚺₁-Predicate good) :
    𝚺₁-Predicate (fun n : M => good (F run ![n,seed]) ∧
      F stepper ![F (clock run cost) ![n,seed],start] = F frame ![F run ![n,seed]]) := by
  let S : M → M := fun n => F run ![n,seed]
  let C : M → M := fun n => F (clock run cost) ![n,seed]
  let L : M → M := fun n => F stepper ![C n,start]
  let R : M → M := fun n => F frame ![S n]
  have hs : 𝚺₁-Function₁ S := bindBinary _ seed (binaryCodeDef (M := M) run)
  have hc : 𝚺₁-Function₁ C := bindBinary _ seed (binaryCodeDef (M := M) (clock run cost))
  have hl : 𝚺₁-Function₁ L := composeUnary _ C (bindBinary _ start (binaryCodeDef (M := M) stepper)) hc
  have hr : 𝚺₁-Function₁ R := composeUnary _ S (unaryCodeDef (M := M) frame) hs
  exact andPred _ _ (composePred good S hgood hs) (equalPred L R hl hr)

#print axioms unaryCodeDef
#print axioms binaryCodeDef
#print axioms invariantDef
end models
end PA194ClockInvariantDefinable
