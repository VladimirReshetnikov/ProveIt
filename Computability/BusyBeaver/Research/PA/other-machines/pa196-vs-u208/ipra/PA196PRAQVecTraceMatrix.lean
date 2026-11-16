import PA196PRAQVecHistory
import DiophantineConsistency.PRAHistoryTrace

/-! A bounded candidate-PRA predicate saying that a sequence contains a
parameterized tower's initial segment. -/
set_option autoImplicit false
namespace PA196PRAQVecTraceMatrix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PRAQVecTower

def traceSeqRew : Rew language Empty 1 Empty 3 := Rew.embSubsts ![#1]
def traceLhRew : Rew language Empty 2 Empty 3 :=
  Rew.embSubsts ![.func addCode ![#0,.func oneCode Fin.elim0],#1]
noncomputable def traceMemRew : Rew language Empty 3 Empty 4 :=
  Rew.embSubsts ![#2,#0,.func towerCode ![#0,#3]]
noncomputable def traceMatrix : Semisentence language 3 :=
  (traceSeqRew ▹ Semiformula.lMap embedding seqDef.val) ⋏
  (traceLhRew ▹ Semiformula.lMap embedding lhDef.val) ⋏
  (∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0,.func addCode ![#1,.func oneCode Fin.elim0]])]
    (traceMemRew ▹ Semiformula.lMap embedding memRel.val))

theorem traceMatrix_bounded : Hierarchy 𝚺 0 traceMatrix := by
  unfold traceMatrix
  apply Hierarchy.and
  · exact Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy seqDef.sigma_prop)
  · apply Hierarchy.and
    · exact Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy lhDef.sigma_prop)
    · apply Hierarchy.ball
      · simp [Semiterm.Positive, Semiterm.bv_func]
      · exact Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy memRel.sigma_prop)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem traceSeq_eval (n h seed : M) :
    (traceSeqRew ▹ Semiformula.lMap embedding seqDef.val).Eval ![n,h,seed] Empty.elim ↔
      seqDef.val.Evalb ![h] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![n,h,seed] Empty.elim ∘ traceSeqRew ∘ Semiterm.bvar) = ![h] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have he : (Semiterm.val (L := language) ![n,h,seed] Empty.elim ∘ traceSeqRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem traceLh_eval (n h seed : M) :
    (traceLhRew ▹ Semiformula.lMap embedding lhDef.val).Eval ![n,h,seed] Empty.elim ↔
      lhDef.val.Evalb ![n+1,h] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![n,h,seed] Empty.elim ∘ traceLhRew ∘ Semiterm.bvar) = ![n+1,h] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) addCode
        (Semiterm.val (L := language) ![n,h,seed] Empty.elim ∘ ![#0,.func oneCode Fin.elim0]) = _
      congr 1
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      change Structure.func (L := language) oneCode
        (Semiterm.val (L := language) ![n,h,seed] Empty.elim ∘ Fin.elim0) = _
      congr 1
      exact Subsingleton.elim _ _
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have he : (Semiterm.val (L := language) ![n,h,seed] Empty.elim ∘ traceLhRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem traceMem_eval (i n h seed : M) :
    (traceMemRew ▹ Semiformula.lMap embedding memRel.val).Eval ![i,n,h,seed] Empty.elim ↔
      memRel.val.Evalb ![h,i,tower i seed] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![i,n,h,seed] Empty.elim ∘ traceMemRew ∘ Semiterm.bvar) =
      ![h,i,tower i seed] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change Structure.func (L := language) towerCode
      (Semiterm.val (L := language) ![i,n,h,seed] Empty.elim ∘ ![#0,#3]) = _
    congr 1
    funext k
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have he : (Semiterm.val (L := language) ![i,n,h,seed] Empty.elim ∘ traceMemRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem trace_eval (n h seed : M) : traceMatrix.Eval ![n,h,seed] Empty.elim ↔
    seqDef.val.Evalb ![h] ∧ lhDef.val.Evalb ![n+1,h] ∧
      ∀ i < n+1, memRel.val.Evalb ![h,i,tower i seed] := by
  have hz (x : M) : (Semiterm.val (L := language) ![x,n,h,seed] Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [traceMatrix, FirstOrder.ball, traceSeq_eval, traceLh_eval, traceMem_eval,
    Semiformula.eval_rel, Semiterm.val_func, hz]
  intro _ _
  rfl
end models
#print axioms traceMatrix_bounded
#print axioms trace_eval
end PA196PRAQVecTraceMatrix
