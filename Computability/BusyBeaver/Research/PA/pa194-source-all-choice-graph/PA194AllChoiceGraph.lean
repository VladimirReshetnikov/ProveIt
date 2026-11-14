import PA194AllFields
/-! Parameter-free Σ₁ composition of Foundation free substitution and the
internal universal-rule selector. This is not a finite candidate-PRA code. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194AllChoiceGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PA194PathIterator PA194AllFields PA194AllChoice PA194ParamComp

noncomputable def body2 : Code 2 := unary body (.proj 0)
def inputNode : Code 2 := .proj 0
def inputTarget : Code 2 := .proj 1
noncomputable def freeBodyGraph : 𝚺₁.Semisentence 3 :=
  compGraph (freeGraph M6.PA.RelationalSource.language) (fun _ => PA194CodeGraph.graph body2)
noncomputable def choiceGraph : 𝚺₁.Semisentence 3 :=
  compGraph (PA194CodeGraph.graph nodeChoice)
    ![PA194CodeGraph.graph inputNode, freeBodyGraph, PA194CodeGraph.graph inputTarget]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem free_body_defined : 𝚺₁.DefinedFunction
    (fun e : Fin 2 → M => free M6.PA.RelationalSource.language (F body2 e)) freeBodyGraph := by
  have hf : 𝚺₁.DefinedFunction (fun e : Fin 1 → M => free M6.PA.RelationalSource.language (e 0))
      (freeGraph M6.PA.RelationalSource.language) := free.defined
  have hg : ∀ i : Fin 1, 𝚺₁.DefinedFunction (fun e : Fin 2 → M => F body2 e) (PA194CodeGraph.graph body2) :=
    fun _ => PA194CodeGraph.modelGraph body2
  have h := compGraph_defined (freeGraph M6.PA.RelationalSource.language)
    (fun _ => PA194CodeGraph.graph body2)
    (fun e : Fin 1 → M => free M6.PA.RelationalSource.language (e 0))
    (fun _ e => F body2 e) hf hg
  exact h

theorem choice_defined : 𝚺₁.DefinedFunction
    (fun e : Fin 2 → M => F nodeChoice ![e 0,free M6.PA.RelationalSource.language (F body2 e),e 1])
    choiceGraph := by
  let G : Fin 3 → (Fin 2 → M) → M := ![fun e => F inputNode e,
    fun e => free M6.PA.RelationalSource.language (F body2 e),fun e => F inputTarget e]
  have hg : ∀ i : Fin 3, 𝚺₁.DefinedFunction (G i)
      (![PA194CodeGraph.graph inputNode,freeBodyGraph,PA194CodeGraph.graph inputTarget] i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact PA194CodeGraph.modelGraph inputNode
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact free_body_defined
      · exact Fin.cases (PA194CodeGraph.modelGraph inputTarget) (fun l => Fin.elim0 l) k
  have h := compGraph_defined (PA194CodeGraph.graph nodeChoice)
    ![PA194CodeGraph.graph inputNode,freeBodyGraph,PA194CodeGraph.graph inputTarget]
    (fun e : Fin 3 → M => F nodeChoice e) G (PA194CodeGraph.modelGraph nodeChoice) hg
  apply HierarchySymbol.DefinedFunction.of_eq _ h
  intro e
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 e
  · refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases (modelProjection 1 e) (fun l => Fin.elim0 l) k

theorem choice_graph_total (d q : M) : ∃ y, choiceGraph.val.Eval ![y,d,q] Empty.elim := by
  let y := F nodeChoice ![d,free M6.PA.RelationalSource.language (F body2 ![d,q]),q]
  have h := (choice_defined (M := M)).defined ![y,d,q]
  have he : (fun i : Fin 2 => ![y,d,q] i.succ) = ![d,q] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simp only [Matrix.cons_val_zero] at h
  rw [he] at h
  exact ⟨y,h.mpr rfl⟩

#print axioms choice_graph_total

theorem all_choice_graph (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    (s p dp q y : M)
    (hdp : DerivationOf T dp (insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s)))
    (hq : q ∈ insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s))
    (hy : choiceGraph.val.Eval ![y,allIntro s p dp,q] Empty.elim) :
    (q = free M6.PA.RelationalSource.language p ∧ y = 0) ∨
      ∃ u, y = u+1 ∧ u ∈ s ∧ shift M6.PA.RelationalSource.language u = q := by
  have h := (choice_defined (M := M)).defined ![y,allIntro s p dp,q]
  have he : (fun i : Fin 2 => ![y,allIntro s p dp,q] i.succ) = ![allIntro s p dp,q] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simp only [Matrix.cons_val_zero] at h
  rw [he] at h
  have hb : F body2 ![allIntro s p dp,q] = p := by
    rw [body2,modelUnary,modelProjection]
    exact (fields_all s p dp).2.2.1
  rw [hb] at h
  have hh := h.mp hy
  change y = F nodeChoice ![allIntro s p dp,free M6.PA.RelationalSource.language p,q] at hh
  rw [hh]
  exact all_node_choice T s p dp q hdp hq

#print axioms all_choice_graph

#print axioms choice_defined
end models
end PA194AllChoiceGraph
