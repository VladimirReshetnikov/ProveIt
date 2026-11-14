import PA194Head1Checker
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194Head1Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PA194Head1Checker PA194TargetCantor
def plusOne : ArithmeticSemiterm Empty 2 := .func .add ![#1, .func .one Fin.elim0]
/-- Inputs are certificate and theorem; the checker output is theorem plus one. -/
noncomputable def certificateGraph : 𝚺₁.Semisentence 2 :=
  (PA194CodeGraph.graph check).rew (Rew.subst ![plusOne,#0])

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

theorem graph_correct (c y : M) :
    (PA194CodeGraph.graph check).val.Eval ![y+1,c] Empty.elim ↔ Head1Certificate c y := by
  have h := (PA194CodeGraph.modelGraph (M := M) check).defined ![y+1,c]
  have he : (fun i : Fin 1 => ![y+1,c] i.succ) = ![c] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp only [Matrix.cons_val_zero] at h
  rw [he] at h
  constructor
  · intro hg
    exact (check_correct c y).mp (h.mp hg).symm
  · intro hc
    exact h.mpr ((check_correct c y).mpr hc).symm

theorem certificate_graph_correct (c y : M) :
    certificateGraph.val.Eval ![c,y] Empty.elim ↔ Head1Certificate c y := by
  change (Rew.subst ![plusOne,#0] ▹ (PA194CodeGraph.graph check).val).Eval ![c,y] Empty.elim ↔ _
  rw [Semiformula.eval_substs]
  have he : (Semiterm.val ![c,y] Empty.elim ∘ ![plusOne,#0]) = ![y+1,c] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Matrix.cons_val_zero, plusOne, Semiterm.val_func, Function.comp_def]
      have hv : (fun j : Fin 2 => Semiterm.val (L := ℒₒᵣ) ![c,y] Empty.elim ((![#1,.func .one Fin.elim0] : Fin 2 → ArithmeticSemiterm Empty 2) j)) = ![y,1] := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
          change (1 : M) = 1
          rfl
      rw [hv]
      rfl
    · exact Fin.cases (by simp) (fun k => Fin.elim0 k) j
  rw [he]
  exact graph_correct c y

#print axioms certificate_graph_correct

#print axioms graph_correct
end models
end PA194Head1Graph
