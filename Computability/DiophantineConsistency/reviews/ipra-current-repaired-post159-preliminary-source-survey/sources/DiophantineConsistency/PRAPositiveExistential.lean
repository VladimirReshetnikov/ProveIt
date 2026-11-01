import DiophantineConsistency.PRAPositivePairMatrix
/-! Pair an original existential variable with the inner witness. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositiveExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAPairedInductionMatrix
  PRAPositiveNormalization PRAPositivePairMatrix PRABoundedPairGraph

def jointMatrix {n : ℕ} (C : Semisentence language (n+2)) : Semisentence language (n+1) :=
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 1, .func oneCode Fin.elim0]])]
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 2, .func oneCode Fin.elim0]])]
    ((Rew.embSubsts ![#2,#1,#0] ▹ pairGraph) ⋏
      (Rew.embSubsts (Fin.cases (#0) (Fin.cases (#1)
        (fun i : Fin n => .bvar i.succ.succ.succ))) ▹ C))

theorem jointMatrix_bounded {n : ℕ} (C : Semisentence language (n+2))
    (hC : Hierarchy 𝚺 0 C) : Hierarchy 𝚺 0 (jointMatrix C) := by
  unfold jointMatrix
  apply Hierarchy.bexs
  · simp [Semiterm.Positive, Semiterm.bv_func]
  · apply Hierarchy.bexs
    · simp [Semiterm.Positive, Semiterm.bv_func]
    · exact Hierarchy.and (Hierarchy.rew _ pairGraph_bounded) (Hierarchy.rew _ hC)

theorem modelJointMatrix {M : Type} [Structure language M] (n : ℕ)
    (C : Semisentence language (n+2)) (t : M) (v : Fin n → M) :
    (jointMatrix C).Eval (Fin.cases t v) Empty.elim ↔
      ∃ a b : M, Structure.rel (L := language) Language.ORing.Rel.lt
        ![a, Structure.func (L := language) addCode
          ![t, Structure.func (L := language) oneCode Fin.elim0]] ∧
        Structure.rel (L := language) Language.ORing.Rel.lt
        ![b, Structure.func (L := language) addCode
          ![t, Structure.func (L := language) oneCode Fin.elim0]] ∧
        pairGraph.Eval ![t,a,b] Empty.elim ∧
        C.Eval (Fin.cases b (Fin.cases a v)) Empty.elim := by
  simp only [jointMatrix, bexs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and]
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
  have hC (a b : M) :
      (Rew.embSubsts (Fin.cases (#0) (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ))) ▹ C).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ↔
          C.Eval (Fin.cases b (Fin.cases a v)) Empty.elim := by
    rw [Semiformula.eval_rew]
    have hv : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
      Rew.embSubsts (Fin.cases (#0) (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ))) ∘
        Semiterm.bvar) = Fin.cases b (Fin.cases a v) := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun _ => rfl) j
    have hf : (Semiterm.val (L := language) (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∘
      Rew.embSubsts (Fin.cases (#0) (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ))) ∘
        Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
    rw [hv,hf]
  change (∃ a : M, (Semiformula.rel Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 1, .func oneCode Fin.elim0]] : Semisentence language (n+2)).Eval
      (Fin.cases a (Fin.cases t v)) Empty.elim ∧
    ∃ b : M, (Semiformula.rel Language.ORing.Rel.lt
      ![.bvar 0, .func addCode ![.bvar 2, .func oneCode Fin.elim0]] : Semisentence language (n+3)).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∧
      (Rew.embSubsts ![#2,#1,#0] ▹ pairGraph).Eval (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim ∧
      (Rew.embSubsts (Fin.cases (#0) (Fin.cases (#1) (fun i : Fin n => .bvar i.succ.succ.succ))) ▹ C).Eval
        (Fin.cases b (Fin.cases a (Fin.cases t v))) Empty.elim) ↔ _
  simp only [he1,he2,hgraph,hC]
  constructor
  · rintro ⟨a,ha,b,hb,hg,hc⟩
    exact ⟨a,b,ha,hb,hg,hc⟩
  · rintro ⟨a,b,ha,hb,hg,hc⟩
    exact ⟨a,ha,b,hb,hg,hc⟩

def normalEx {n : ℕ} {φ : Semisentence language (n+1)} (a : Normal φ) : Normal (∃⁰ φ) where
  matrix := jointMatrix a.matrix
  bounded := jointMatrix_bounded a.matrix a.bounded
  correct := by
    intro M _ _ _ _ v
    simp only [Semiformula.eval_ex]
    have hv (z : M) : (z :> v) = Fin.cases z v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    constructor
    · rintro ⟨z,hz⟩
      rw [hv z] at hz
      obtain ⟨w,hw⟩ := (a.correct M (Fin.cases z v)).mp hz
      obtain ⟨t,hgraph,_,hzb,hwb⟩ := modelPairGraphBounded z w
      refine ⟨t,(modelJointMatrix n a.matrix t v).mpr ?_⟩
      exact ⟨z,w,hzb,hwb,hgraph,hw⟩
    · rintro ⟨t,ht⟩
      obtain ⟨z,w,_,_,_,hw⟩ := (modelJointMatrix n a.matrix t v).mp ht
      refine ⟨z, ?_⟩
      rw [hv z]
      exact (a.correct M (Fin.cases z v)).mpr ⟨w,hw⟩
end DiophantineConsistency.PRAPositiveExistential
