import DiophantineConsistency.PRAPositiveNormalization
import DiophantineConsistency.PRABoundedPairGraph
/-! Bounded graph for combining two witnesses without collection. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositivePairMatrix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAPairedInductionMatrix
  PRAPositiveNormalization PRABoundedPairGraph

def pairMatrix {n : ℕ} (A B : Semisentence language (n+1)) : Semisentence language (n+1) :=
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 1, .func oneCode Fin.elim0]])]
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 2, .func oneCode Fin.elim0]])]
    ((Rew.embSubsts ![#2,#1,#0] ▹ pairGraph) ⋏
      ((Rew.embSubsts (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ)) ▹ A) ⋏
       (Rew.embSubsts (Fin.cases (#0) (fun i : Fin n => .bvar i.succ.succ.succ)) ▹ B)))

theorem pairMatrix_bounded {n : ℕ} (A B : Semisentence language (n+1))
    (hA : Hierarchy 𝚺 0 A) (hB : Hierarchy 𝚺 0 B) : Hierarchy 𝚺 0 (pairMatrix A B) := by
  unfold pairMatrix
  apply Hierarchy.bexs
  · simp [Semiterm.Positive, Semiterm.bv_func]
  · apply Hierarchy.bexs
    · simp [Semiterm.Positive, Semiterm.bv_func]
    · apply Hierarchy.and
      · exact Hierarchy.rew _ pairGraph_bounded
      · exact Hierarchy.and (Hierarchy.rew _ hA) (Hierarchy.rew _ hB)

theorem modelPairMatrix {M : Type} [Structure language M] (n : ℕ)
    (A B : Semisentence language (n+1)) (t : M) (v : Fin n → M) :
    (pairMatrix A B).Eval (Fin.cases t v) Empty.elim ↔
      ∃ a b : M, Structure.rel (L := language) Language.ORing.Rel.lt
        ![a, Structure.func (L := language) addCode
          ![t, Structure.func (L := language) oneCode Fin.elim0]] ∧
        Structure.rel (L := language) Language.ORing.Rel.lt
        ![b, Structure.func (L := language) addCode
          ![t, Structure.func (L := language) oneCode Fin.elim0]] ∧
        pairGraph.Eval ![t,a,b] Empty.elim ∧
        A.Eval (Fin.cases a v) Empty.elim ∧ B.Eval (Fin.cases b v) Empty.elim := by
  simp only [pairMatrix, bexs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and]
  have he1 (a : M) :
      (Semiformula.rel Language.ORing.Rel.lt
        ![.bvar 0, .func addCode ![.bvar 1, .func oneCode Fin.elim0]] : Semisentence language (n+2)).Eval
          (Fin.cases a (Fin.cases t v)) Empty.elim ↔
        Structure.rel (L := language) Language.ORing.Rel.lt
          ![a,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] := by
    simp only [Semiformula.eval_rel]
    have hz : (Semiterm.val (L := language) (Fin.cases a (Fin.cases t v)) Empty.elim ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    have ha : (Semiterm.val (L := language) (Fin.cases a (Fin.cases t v)) Empty.elim ∘
        ![.bvar 1, .func oneCode Fin.elim0]) =
        ![t,Structure.func (L := language) oneCode Fin.elim0] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) oneCode (Semiterm.val _ Empty.elim ∘ Fin.elim0) = _
      rw [hz]
      rfl
    simp [Semiterm.val_func, ha]
  have he2 (a b : M) :
      (Semiformula.rel Language.ORing.Rel.lt
        ![.bvar 0, .func addCode ![.bvar 2, .func oneCode Fin.elim0]] : Semisentence language (n+3)).Eval
          (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ↔
        Structure.rel (L := language) Language.ORing.Rel.lt
          ![b,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] := by
    simp only [Semiformula.eval_rel]
    have hz : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    have ha : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
        ![.bvar 2, .func oneCode Fin.elim0]) =
        ![t,Structure.func (L := language) oneCode Fin.elim0] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) oneCode (Semiterm.val _ Empty.elim ∘ Fin.elim0) = _
      rw [hz]
      rfl
    simp [Semiterm.val_func, ha]
  have hgraph (a b : M) :
      (Rew.embSubsts ![#2,#1,#0] ▹ pairGraph).Eval (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ↔
        pairGraph.Eval ![t,a,b] Empty.elim := by
    rw [Semiformula.eval_rew]
    have hv : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
        Rew.embSubsts ![#2,#1,#0] ∘ Semiterm.bvar) = ![t,a,b] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
    have hf : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
        Rew.embSubsts ![#2,#1,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
    rw [hv,hf]
  have hA (a b : M) :
      (Rew.embSubsts (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ)) ▹ A).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ↔ A.Eval (Fin.cases a v) Empty.elim := by
    rw [Semiformula.eval_rew]
    have hv : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
      Rew.embSubsts (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ)) ∘ Semiterm.bvar) = Fin.cases a v := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    have hf : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
      Rew.embSubsts (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ)) ∘ Semiterm.fvar) =
        (Empty.elim : Empty → M) := Subsingleton.elim _ _
    rw [hv,hf]
  have hB (a b : M) :
      (Rew.embSubsts (Fin.cases (#0) (fun i : Fin n => .bvar i.succ.succ.succ)) ▹ B).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ↔ B.Eval (Fin.cases b v) Empty.elim := by
    rw [Semiformula.eval_rew]
    have hv : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
      Rew.embSubsts (Fin.cases (#0) (fun i : Fin n => .bvar i.succ.succ.succ)) ∘ Semiterm.bvar) = Fin.cases b v := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    have hf : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
      Rew.embSubsts (Fin.cases (#0) (fun i : Fin n => .bvar i.succ.succ.succ)) ∘ Semiterm.fvar) =
        (Empty.elim : Empty → M) := Subsingleton.elim _ _
    rw [hv,hf]
  change (∃ a : M, (Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 1, .func oneCode Fin.elim0]] : Semisentence language (n+2)).Eval
      (Fin.cases a (Fin.cases t v)) Empty.elim ∧
    ∃ b : M, (Semiformula.rel Language.ORing.Rel.lt
      ![.bvar 0, .func addCode ![.bvar 2, .func oneCode Fin.elim0]] : Semisentence language (n+3)).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∧
      (Rew.embSubsts ![#2,#1,#0] ▹ pairGraph).Eval (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∧
      (Rew.embSubsts (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ)) ▹ A).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∧
      (Rew.embSubsts (Fin.cases (#0) (fun i : Fin n => .bvar i.succ.succ.succ)) ▹ B).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim) ↔ _
  simp only [he1,he2,hgraph,hA,hB]
  constructor
  · rintro ⟨a,ha,b,hb,hg,hav,hbv⟩
    exact ⟨a,b,ha,hb,hg,hav,hbv⟩
  · rintro ⟨a,b,ha,hb,hg,hav,hbv⟩
    exact ⟨a,ha,b,hb,hg,hav,hbv⟩

/-- Two normalized witnesses combine into one using the bounded pair graph. -/
def normalAnd {n : ℕ} {φ ψ : Semisentence language n} (a : Normal φ) (b : Normal ψ) : Normal (φ ⋏ ψ) where
  matrix := pairMatrix a.matrix b.matrix
  bounded := pairMatrix_bounded a.matrix b.matrix a.bounded b.bounded
  correct := by
    intro M _ _ _ _ v
    change (φ.Eval v Empty.elim ∧ ψ.Eval v Empty.elim) ↔
      ∃ t : M, (pairMatrix a.matrix b.matrix).Eval (Fin.cases t v) Empty.elim
    rw [a.correct M v,b.correct M v]
    constructor
    · rintro ⟨⟨u,hu⟩,⟨w,hw⟩⟩
      obtain ⟨t,hgraph,_,hub,hwb⟩ := modelPairGraphBounded u w
      refine ⟨t,(modelPairMatrix n a.matrix b.matrix t v).mpr ?_⟩
      exact ⟨u,w,hub,hwb,hgraph,hu,hw⟩
    · rintro ⟨t,ht⟩
      obtain ⟨u,w,_,_,_,hu,hw⟩ := (modelPairMatrix n a.matrix b.matrix t v).mp ht
      exact ⟨⟨u,hu⟩,⟨w,hw⟩⟩
end DiophantineConsistency.PRAPositivePairMatrix
