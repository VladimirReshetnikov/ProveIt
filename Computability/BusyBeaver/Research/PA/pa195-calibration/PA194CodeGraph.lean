import PA194ParamComp
import PA194ParamRecursionDefined
/-! Uniform arithmetic Σ₁ graphs for every finite candidate-PRA code.

`graph c` is independent of the model.  `modelGraph` proves agreement with
its interpretation on all tuples, including nonstandard elements, in each
candidate-PRA model whose arithmetic reduct satisfies IΣ₁.  It does not by
itself prove either machine-consistency implication.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194CodeGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194ParamComp

def precBlueprint {n : ℕ} (φ : 𝚺₁.Semisentence (n+1))
    (ψ : 𝚺₁.Semisentence (n+3)) : PR.Blueprint n where
  zero := φ
  succ := ψ.rew (Rew.embSubsts (#0 :> #2 :> #1 :> fun i => #i.succ.succ.succ))

mutual
def graph : {n : ℕ} → Code n → 𝚺₁.Semisentence (n+1)
  | n, .zero _ => .mkSigma “#0 = 0”
  | _, .succ => .mkSigma “y x. y = x + 1”
  | _, .proj i => .mkSigma “#0 = #i.succ”
  | _, .comp f g => compGraph (graph f) (graphs g)
  | _, .prec f g => (precBlueprint (graph f) (graph g)).resultDef

def graphs : {n m : ℕ} → Codes n m → Fin m → 𝚺₁.Semisentence (n+1)
  | _, _, .nil _, i => Fin.elim0 i
  | _, _, .cons h t, i => Fin.cases (graph h) (graphs t) i
end


section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem stepGraph_defined {n : ℕ} (φ : 𝚺₁.Semisentence (n+1)) (ψ : 𝚺₁.Semisentence (n+3))
    (G : (Fin (n+2) → M) → M) (hG : 𝚺₁.DefinedFunction G ψ) :
    𝚺₁.DefinedFunction (fun e : Fin (n+2) → M =>
      G (Fin.cases (e 1) (Fin.cases (e 0) (fun i => e i.succ.succ))))
      (precBlueprint φ ψ).succ := by
  apply HierarchySymbol.Defined.mk
  intro e
  simp [precBlueprint, Semiformula.eval_embSubsts, hG.iff, Function.comp_def]
  have he : (fun x : Fin (n+2) => Semiterm.val e Empty.elim
      (((#2 :> #1 :> fun i => #i.succ.succ.succ) : Fin (n+2) → ArithmeticSemiterm Empty (n+3)) x)) =
      Fin.cases (e 2) (Fin.cases (e 1) (fun i => e i.succ.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun l => rfl) j
  rw [he]

mutual
/-- Every finite candidate-PRA code has an arithmetic Σ₁ graph throughout
any candidate-PRA model whose arithmetic reduct satisfies IΣ₁. -/
theorem modelGraph : {n : ℕ} → (c : Code n) →
    𝚺₁.DefinedFunction (fun e : Fin n → M => F c e) (graph c)
  | _, .zero _ => by
      apply HierarchySymbol.Defined.mk
      intro e
      change _ ↔ e 0 = F (.zero _) _
      rw [PRAMultiplication.modelZero]
      change _ ↔ e 0 = (0 : M)
      simp [graph]
  | _, .succ => by
      apply HierarchySymbol.Defined.mk
      intro e
      change _ ↔ e 0 = F .succ _
      have hv : (fun i : Fin 1 => e i.succ) = (fun _ => e 1) := by
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      rw [hv, ←modelAddOne]
      change _ ↔ e 0 = e 1 + 1
      simp [graph]
  | _, .proj i => by
      apply HierarchySymbol.Defined.mk
      intro e
      change _ ↔ e 0 = F (.proj i) _
      rw [modelProjection]
      simp [graph]
  | _, .comp f g => by
      have hf := modelGraph f
      have hg := modelGraphs g
      have h := compGraph_defined (graph f) (graphs g) (fun e => F f e)
        (fun i e => F (getCode g i) e) hf hg
      apply HierarchySymbol.DefinedFunction.of_eq _ h
      intro e
      exact (modelComposition f g e).symm
  | _, .prec f g => by
      let B := precBlueprint (graph f) (graph g)
      let c : PR.Construction M B := {
        zero := fun v => F f v
        succ := fun v i z => F g (Fin.cases i (Fin.cases z v))
        zero_defined := modelGraph f
        succ_defined := stepGraph_defined (graph f) (graph g) (fun e => F g e) (modelGraph g)
      }
      exact PA194ParamRecursionDefined.model_defined B c f g (fun _ => rfl) (fun _ _ _ => rfl)

theorem modelGraphs : {n m : ℕ} → (g : Codes n m) → ∀ i,
    𝚺₁.DefinedFunction (fun e : Fin n → M => F (getCode g i) e) (graphs g i)
  | _, _, .nil _, i => Fin.elim0 i
  | _, _, .cons h t, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact modelGraph h
      · exact modelGraphs t j
end

#print axioms modelGraph
end models
#print axioms graph
end PA194CodeGraph
