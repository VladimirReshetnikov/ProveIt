import PA194ParamIterator
import DiophantineConsistency.PRAHistoryTrace
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ParamTrace
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryTrace
  PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
open PA194ParamIterator

def traceSeqRew (k : ℕ) : Rew language Empty 1 Empty (k+2) := Rew.embSubsts ![#1]
def traceLhRew (k : ℕ) : Rew language Empty 2 Empty (k+2) := Rew.embSubsts ![.func addCode ![#0,.func oneCode Fin.elim0],#1]
def traceMemRew {k : ℕ} (value : Code (k+1)) : Rew language Empty 3 Empty (k+3) :=
  Rew.embSubsts ![#2,#0,.func value (Fin.cases #0 (fun j => #j.succ.succ.succ))]

def traceMatrix {k : ℕ} (value : Code (k+1)) : Semisentence language (k+2) :=
  (traceSeqRew k ▹ Semiformula.lMap embedding seqDef.val) ⋏
  (traceLhRew k ▹ Semiformula.lMap embedding lhDef.val) ⋏
  (∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0,.func addCode ![#1,.func oneCode Fin.elim0]])]
    (traceMemRew value ▹ Semiformula.lMap embedding memRel.val))

theorem traceMatrix_bounded {k : ℕ} (value : Code (k+1)) : Hierarchy 𝚺 0 (traceMatrix value) := by
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
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem traceSeq_eval (k : ℕ) (n h : M) (v : Fin k → M) :
    (traceSeqRew k ▹ Semiformula.lMap embedding seqDef.val).Eval (Fin.cases n (Fin.cases h v)) Empty.elim ↔
      seqDef.val.Evalb ![h] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) (Fin.cases n (Fin.cases h v)) Empty.elim ∘ traceSeqRew k ∘ Semiterm.bvar) = ![h] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have he : (Semiterm.val (L := language) (Fin.cases n (Fin.cases h v)) Empty.elim ∘ traceSeqRew k ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem traceLh_eval (k : ℕ) (n h : M) (v : Fin k → M) :
    (traceLhRew k ▹ Semiformula.lMap embedding lhDef.val).Eval (Fin.cases n (Fin.cases h v)) Empty.elim ↔
      lhDef.val.Evalb ![n+1,h] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) (Fin.cases n (Fin.cases h v)) Empty.elim ∘ traceLhRew k ∘ Semiterm.bvar) = ![n+1,h] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change F addCode
        (Semiterm.val (L := language) (Fin.cases n (Fin.cases h v)) Empty.elim ∘ ![#0,.func oneCode Fin.elim0]) = _
      congr 1
      funext j
      refine Fin.cases rfl (fun l => ?_) j
      refine Fin.cases ?_ (fun l => Fin.elim0 l) l
      change F oneCode (Semiterm.val (L := language) (Fin.cases n (Fin.cases h v)) Empty.elim ∘ Fin.elim0) = _
      congr 1
      exact Subsingleton.elim _ _
    · exact Fin.cases rfl (fun l => Fin.elim0 l) j
  have he : (Semiterm.val (L := language) (Fin.cases n (Fin.cases h v)) Empty.elim ∘ traceLhRew k ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem traceMem_eval {k : ℕ} (value : Code (k+1)) (i n h : M) (v : Fin k → M) :
    (traceMemRew value ▹ Semiformula.lMap embedding memRel.val).Eval (Fin.cases i (Fin.cases n (Fin.cases h v))) Empty.elim ↔
      memRel.val.Evalb ![h,i,F value (Fin.cases i v)] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) (Fin.cases i (Fin.cases n (Fin.cases h v))) Empty.elim ∘ traceMemRew value ∘ Semiterm.bvar) =
      ![h,i,F value (Fin.cases i v)] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change F value (Semiterm.val (L := language) (Fin.cases i (Fin.cases n (Fin.cases h v))) Empty.elim ∘
      Fin.cases #0 (fun j => #j.succ.succ.succ)) = _
    congr 1
    funext j
    exact Fin.cases rfl (fun l => rfl) j
  have he : (Semiterm.val (L := language) (Fin.cases i (Fin.cases n (Fin.cases h v))) Empty.elim ∘ traceMemRew value ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem trace_eval {k : ℕ} (value : Code (k+1)) (n h : M) (v : Fin k → M) :
    (traceMatrix value).Eval (Fin.cases n (Fin.cases h v)) Empty.elim ↔
    seqDef.val.Evalb ![h] ∧ lhDef.val.Evalb ![n+1,h] ∧
      ∀ i < n+1, memRel.val.Evalb ![h,i,F value (Fin.cases i v)] := by
  simp [traceMatrix, FirstOrder.ball, traceSeq_eval, traceLh_eval,
    Semiformula.eval_rel, Semiterm.val_func]
  intro _ _
  constructor
  · intro H x hx
    have hm := H x
    have hh (q : Fin 0 → M) : q = Fin.elim0 := Subsingleton.elim _ _
    simp only [hh] at hm
    change x < n+1 → (traceMemRew value ▹ Semiformula.lMap embedding memRel.val).Eval
      (Fin.cases x (Fin.cases n (Fin.cases h v))) Empty.elim at hm
    exact (traceMem_eval value x n h v).mp (hm hx)
  · intro H x
    have hh (q : Fin 0 → M) : q = Fin.elim0 := Subsingleton.elim _ _
    simp only [hh]
    change x < n+1 → (traceMemRew value ▹ Semiformula.lMap embedding memRel.val).Eval
      (Fin.cases x (Fin.cases n (Fin.cases h v))) Empty.elim
    intro hx
    exact (traceMem_eval value x n h v).mpr (H x hx)

theorem modelTraceBase {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2))
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (v : Fin k → M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    (traceMatrix (.prec base step)).Eval
      (Fin.cases (0 : M) (Fin.cases (F (firstHistory cons base) v) v)) Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  let x : M := F base v
  let h : M := F (firstHistory cons base) v
  have hh : h = F cons ![(0 : M),x] := by
    dsimp only [h,x]
    rw [modelFirstHistory, PRAMultiplication.modelZero]
    rfl
  have hc := modelSeqCons cons hcons 0 x
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hc
  have hgraph : seqConsDef.val.Evalb ![h,0,x] := by rw [hh]; exact hc
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := F PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hseq,hlh⟩ := PRAHistorySingletonSequence.singleton_sequence hexp h x hgraph
  rw [trace_eval]
  refine ⟨hseq,by simpa using hlh,?_⟩
  intro i hi
  have hi0 : i = 0 := by
    have : i ≤ 0 := lt_succ_iff_le.mp (by simpa using hi)
    exact le_antisymm this (by simp)
  have hm := PRAHistorySingletonMembership.singleton_memRel hexp h x hgraph i
    (F (.prec base step) (Fin.cases i v))
  apply hm.mpr
  refine ⟨hi0,?_⟩
  rw [hi0]
  change F (.prec base step) (Fin.cases (F (.zero 0) Fin.elim0) v) = x
  exact modelBase base step v

theorem modelTraceStep {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2))
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n h : M) (v : Fin k → M)
    (htrace : (traceMatrix (.prec base step)).Eval (Fin.cases n (Fin.cases h v)) Empty.elim) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    (traceMatrix (.prec base step)).Eval
      (Fin.cases (F Code.succ (fun _ => n))
        (Fin.cases (F (historyStep cons base step) (Fin.cases n (Fin.cases h v))) v)) Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  let x : M := F (.prec base step) (Fin.cases (F Code.succ (fun _ => n)) v)
  let t : M := F cons ![h,x]
  have hc := modelSeqCons cons hcons h x
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hc
  have hgraph : seqConsDef.val.Evalb ![t,h,x] := hc
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := F PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hseq,hlh,hmem⟩ := (trace_eval _ n h v).mp htrace
  have hs := PRAHistoryLengthUnique.modelAppendLength t h x (n+1) hseq hlh hgraph
  obtain ⟨l,_,hld,hm⟩ := PRAHistorySeqConsMembership.seqCons_membership hexp t h x hgraph
  have heq : l = n+1 := PRAHistoryLengthUnique.modelLengthUnique h l (n+1) hld hlh
  rw [heq] at hm
  rw [PA194ParamIterator.modelHistoryStepValue]
  change (traceMatrix (.prec base step)).Eval
    (Fin.cases (F Code.succ (fun _ => n)) (Fin.cases t v)) Empty.elim
  rw [←modelAddOne]
  change (traceMatrix (.prec base step)).Eval (Fin.cases (n+1) (Fin.cases t v)) Empty.elim
  apply (trace_eval _ (n+1) t v).mpr
  refine ⟨hs.1,by simpa [add_assoc] using hs.2,?_⟩
  intro i hi
  have hi' : i ≤ n+1 := lt_succ_iff_le.mp (by simpa [add_assoc] using hi)
  rcases le_iff_lt_or_eq.mp hi' with hlt | heq'
  · exact (hm i _).mpr (Or.inr (hmem i hlt))
  · have hx : F (.prec base step) (Fin.cases i v) = x := by
      rw [heq']
      dsimp only [x]
      rw [←modelAddOne]
      rfl
    exact (hm i _).mpr (Or.inl ⟨heq',hx⟩)


/-- The candidate-PRA history traces every stage, even for nonstandard
parameters and nonstandard recursion time. -/
theorem modelTraceHistory {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2))
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n : M) (v : Fin k → M) :
    (traceMatrix (.prec base step)).Eval
      (Fin.cases n (Fin.cases (F (historyCode cons base step) (Fin.cases n v)) v)) Empty.elim := by
  obtain ⟨pred,_,_,hpred⟩ := PRA_proves_boundedBooleanCharacteristic
    (traceMatrix (.prec base step)) (traceMatrix_bounded _)
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hpred
  have hc := (oneCorrectSentence_iff pred (traceMatrix (.prec base step))).mp hm
  let e : ℕ → M := fun j => if h : j < k then v ⟨j,h⟩ else 0
  have he : (fun i : Fin k => e i.val) = v := by
    funext i
    simp [e, i.isLt]
  have hbase : F pred
      (Fin.cases (F (.zero 0) Fin.elim0)
        (Fin.cases (F (firstHistory cons base) (fun i : Fin k => e i.val))
          (fun i : Fin k => e i.val))) = F oneCode Fin.elim0 := by
    rw [he]
    exact (hc _).mpr (modelTraceBase cons base step hcons v)
  have hstep : ∀ x y : M, F pred
      (Fin.cases x (Fin.cases y (fun i : Fin k => e i.val))) = F oneCode Fin.elim0 →
      F pred (Fin.cases (F Code.succ (fun _ => x))
        (Fin.cases (F (historyStep cons base step)
          (Fin.cases x (Fin.cases y (fun i : Fin k => e i.val))))
          (fun i : Fin k => e i.val))) = F oneCode Fin.elim0 := by
    intro x y hy
    rw [he] at hy ⊢
    apply (hc _).mpr
    exact modelTraceStep cons base step hcons x y v ((hc _).mp hy)
  have h := PRAPrimitiveRecursionInduction.modelRecursiveWitness (M := M) pred
    (firstHistory cons base) (historyStep cons base step) e hbase hstep n
  rw [he] at h
  change F pred (Fin.cases n (Fin.cases (F (historyCode cons base step) (Fin.cases n v)) v)) = _ at h
  exact (hc _).mp h

#print axioms modelTraceHistory
#print axioms modelTraceBase
#print axioms modelTraceStep
end models
end PA194ParamTrace
