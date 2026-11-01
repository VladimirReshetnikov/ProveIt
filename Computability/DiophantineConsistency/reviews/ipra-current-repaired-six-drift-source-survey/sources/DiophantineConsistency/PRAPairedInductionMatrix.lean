import DiophantineConsistency.ParsonsHierarchyMap
import DiophantineConsistency.PRABoundedOneInduction
import Foundation.FirstOrder.Arithmetic.IOpen.Basic
/-! A bounded tagged matrix using Foundation's pairing graph. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPairedInductionMatrix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation

def pairGraph : Semisentence language 3 := Semiformula.lMap embedding pairDef.val

theorem pairGraph_bounded : Hierarchy 𝚺 0 pairGraph := by
  exact ParsonsHierarchyMap.hierarchy pairDef.sigma_prop

/-- Before the bounded existential the slots are `[x,y,t]`; inside it they
are `[c,x,y,t]`. The pairing graph takes `[t,tag,c]`. -/
def branch (ψ : Semisentence language 3) (tag : Code 0) : Semisentence language 3 :=
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 3, .func oneCode Fin.elim0]])]
    ((Rew.embSubsts ![#3,.func tag Fin.elim0,#0] ▹ pairGraph) ⋏
      (Rew.embSubsts ![#1,#2,#0] ▹ ψ))

def pairedMatrix (ψ₀ ψ₁ : Semisentence language 3) : Semisentence language 3 :=
  branch ψ₀ (Code.zero 0) ⋎ branch ψ₁ oneCode

theorem branch_bounded (ψ : Semisentence language 3) (hψ : Hierarchy 𝚺 0 ψ) (tag : Code 0) :
    Hierarchy 𝚺 0 (branch ψ tag) := by
  unfold branch
  apply Hierarchy.bexs
  · simp [Semiterm.Positive, Semiterm.bv_func]
  · apply Hierarchy.and
    · exact Hierarchy.rew _ pairGraph_bounded
    · exact Hierarchy.rew _ hψ

theorem pairedMatrix_bounded (ψ₀ ψ₁ : Semisentence language 3)
    (h₀ : Hierarchy 𝚺 0 ψ₀) (h₁ : Hierarchy 𝚺 0 ψ₁) :
    Hierarchy 𝚺 0 (pairedMatrix ψ₀ ψ₁) :=
  Hierarchy.or (branch_bounded ψ₀ h₀ _) (branch_bounded ψ₁ h₁ _)
/-- The branch's bounded existential has the intended graph and matrix
semantics in every candidate-language structure. -/
theorem branch_eval {M : Type} [Structure language M] (ψ : Semisentence language 3)
    (tag : Code 0) (x y t : M) : (branch ψ tag).Eval ![x,y,t] Empty.elim ↔
      ∃ c : M, Structure.rel (L := language) Language.ORing.Rel.lt
          ![c, Structure.func (L := language) addCode
            ![t,Structure.func (L := language) oneCode Fin.elim0]] ∧
        pairGraph.Eval ![t, Structure.func (L := language) tag Fin.elim0, c] Empty.elim ∧
        ψ.Eval ![x,y,c] Empty.elim := by
  simp only [branch, bexs, Semiformula.eval_ex]
  apply exists_congr
  intro c
  have h1 : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘
      ![.bvar 3, .func oneCode Fin.elim0]) =
      ![t, Structure.func (L := language) oneCode Fin.elim0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    change Structure.func (L := language) oneCode (Semiterm.val ![c,x,y,t] Empty.elim ∘ Fin.elim0) = _
    congr 1
    exact Subsingleton.elim _ _
  have ht : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hp : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘
      ![#3,.func tag Fin.elim0,#0]) =
      ![t,Structure.func (L := language) tag Fin.elim0,c] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => ?_) j
    · change Structure.func (L := language) tag (Semiterm.val ![c,x,y,t] Empty.elim ∘ Fin.elim0) = _
      rw [ht]
      rfl
    · exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hf : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘ ![#1,#2,#0]) = ![x,y,c] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hp' : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#3,.func tag Fin.elim0,#0] ∘ Semiterm.bvar) =
      ![t,Structure.func (L := language) tag Fin.elim0,c] := by
    simpa only [Function.comp_def, Rew.embSubsts_bvar] using hp
  have hf' : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#1,#2,#0] ∘ Semiterm.bvar) = ![x,y,c] := by
    simpa only [Function.comp_def, Rew.embSubsts_bvar] using hf
  have he1 : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#3,.func tag Fin.elim0,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  have he2 : (Semiterm.val (L := language) ![c,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#1,#2,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp [Semiformula.eval_rel, Semiformula.eval_rew, Semiterm.val_func, h1,hp',hf',he1,he2]
end DiophantineConsistency.PRAPairedInductionMatrix
