import DiophantineConsistency.PRABoundedPairGraph
import DiophantineConsistency.ParsonsHierarchyMap
set_option autoImplicit false
namespace DiophantineConsistency.PRATwoParameterPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

def graph : Semisentence language 3 := Semiformula.lMap embedding pairDef.val

/-- Replace two parameter slots by a single code, decoding both by bounded graph witnesses. -/
def packed (ψ : Semisentence language 4) : Semisentence language 3 :=
  ∃⁰[(Semiformula.rel (L := language) Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 3, .func oneCode Fin.elim0]])]
  ∃⁰[(Semiformula.rel (L := language) Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 4, .func oneCode Fin.elim0]])]
    ((Rew.embSubsts ![#4,#1,#0] ▹ graph) ⋏
      (Rew.embSubsts ![#2,#3,#1,#0] ▹ ψ))

theorem packed_bounded (ψ : Semisentence language 4) (hψ : Hierarchy 𝚺 0 ψ) :
    Hierarchy 𝚺 0 (packed ψ) := by
  unfold packed
  apply Hierarchy.bexs
  · simp [Semiterm.Positive, Semiterm.bv_func]
  · apply Hierarchy.bexs
    · simp [Semiterm.Positive, Semiterm.bv_func]
    · apply Hierarchy.and
      · exact Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy pairDef.sigma_prop)
      · exact Hierarchy.rew _ hψ
theorem packed_eval {M : Type} [Structure language M] (ψ : Semisentence language 4)
    (x y t : M) : (packed ψ).Eval ![x,y,t] Empty.elim ↔
      ∃ a b : M,
        Structure.rel (L := language) Language.ORing.Rel.lt
          ![a, Structure.func (L := language) addCode
            ![t,Structure.func (L := language) oneCode Fin.elim0]] ∧
        Structure.rel (L := language) Language.ORing.Rel.lt
          ![b, Structure.func (L := language) addCode
            ![t,Structure.func (L := language) oneCode Fin.elim0]] ∧
        graph.Eval ![t,a,b] Empty.elim ∧ ψ.Eval ![x,y,a,b] Empty.elim := by
  simp only [packed, bexs, Semiformula.eval_ex]
  apply exists_congr
  intro a
  change ((Semiformula.rel (L := language) Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 3, .func oneCode Fin.elim0]]).Eval ![a,x,y,t] Empty.elim ∧
      ∃ b : M, (Semiformula.rel (L := language) Language.ORing.Rel.lt
        ![.bvar 0, .func addCode ![.bvar 4, .func oneCode Fin.elim0]]).Eval ![b,a,x,y,t] Empty.elim ∧
      ((Rew.embSubsts ![#4,#1,#0] ▹ graph).Eval ![b,a,x,y,t] Empty.elim) ∧
      ((Rew.embSubsts ![#2,#3,#1,#0] ▹ ψ).Eval ![b,a,x,y,t] Empty.elim)) ↔ _
  have hfun (b : M) : (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#4,#1,#0] ∘ Semiterm.bvar) = ![t,a,b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hpsi (b : M) : (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#2,#3,#1,#0] ∘ Semiterm.bvar) = ![x,y,a,b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have hb1 : (Semiterm.val (L := language) ![a,x,y,t] Empty.elim ∘
      ![#0,.func addCode ![#3,.func oneCode Fin.elim0]]) =
      ![a,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) addCode
      (Semiterm.val (L := language) ![a,x,y,t] Empty.elim ∘ ![#3,.func oneCode Fin.elim0]) = _
    congr 1
    funext k
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change Structure.func (L := language) oneCode (Semiterm.val (L := language) ![a,x,y,t] Empty.elim ∘ Fin.elim0) = _
    congr 1
    exact Subsingleton.elim _ _
  have hb2 (b : M) : (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘
      ![#0,.func addCode ![#4,.func oneCode Fin.elim0]]) =
      ![b,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) addCode
      (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘ ![#4,.func oneCode Fin.elim0]) = _
    congr 1
    funext k
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change Structure.func (L := language) oneCode (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘ Fin.elim0) = _
    congr 1
    exact Subsingleton.elim _ _
  have hgfree (b : M) : (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#4,#1,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  have hpfree (b : M) : (Semiterm.val (L := language) ![b,a,x,y,t] Empty.elim ∘
      Rew.embSubsts ![#2,#3,#1,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp only [Semiformula.eval_rel, Semiformula.eval_rew, hb1, hb2, hfun, hpsi, hgfree, hpfree]
  constructor
  · rintro ⟨ha,b,hb,hg,hψ⟩; exact ⟨b,ha,hb,hg,hψ⟩
  · rintro ⟨b,ha,hb,hg,hψ⟩; exact ⟨ha,b,hb,hg,hψ⟩

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

/-- In every candidate-PRA model, one code uniformly recovers any chosen pair. -/
theorem modelPacking (ψ : Semisentence language 4) (a b : M) :
    ∃ t : M, ∀ x y : M, (packed ψ).Eval ![x,y,t] Empty.elim ↔ ψ.Eval ![x,y,a,b] Empty.elim := by
  obtain ⟨t,hgraph,hunique,ha,hb⟩ := PRABoundedPairGraph.modelPairGraphBounded a b
  refine ⟨t, fun x y => ?_⟩
  rw [packed_eval]
  constructor
  · rintro ⟨c,d,_,_,hc,hd⟩
    have he := hunique c d hc
    simpa [he.1,he.2] using hd
  · intro h
    exact ⟨a,b,ha,hb,hgraph,h⟩
end models
end DiophantineConsistency.PRATwoParameterPacking
