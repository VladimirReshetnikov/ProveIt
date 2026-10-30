import DiophantineConsistency.PRAHistoryLengthUnique
import DiophantineConsistency.PRAHistorySingletonSequence
import DiophantineConsistency.PRAHistoryIterator
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryTrace
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryIterator
  PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness

def traceSeqRew : Rew language Empty 1 Empty 2 := Rew.embSubsts ![#1]
def traceLhRew : Rew language Empty 2 Empty 2 := Rew.embSubsts ![.func addCode ![#0,.func oneCode Fin.elim0],#1]
def traceMemRew (value : Code 1) : Rew language Empty 3 Empty 3 :=
  Rew.embSubsts ![#2,#0,.func value ![#0]]

def traceMatrix (value : Code 1) : Semisentence language 2 :=
  (traceSeqRew ▹ Semiformula.lMap embedding seqDef.val) ⋏
  (traceLhRew ▹ Semiformula.lMap embedding lhDef.val) ⋏
  (∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0,.func addCode ![#1,.func oneCode Fin.elim0]])]
    (traceMemRew value ▹ Semiformula.lMap embedding memRel.val))

theorem traceMatrix_bounded (value : Code 1) : Hierarchy 𝚺 0 (traceMatrix value) := by
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
theorem traceSeq_eval (n h : M) :
    (traceSeqRew ▹ Semiformula.lMap embedding seqDef.val).Eval ![n,h] Empty.elim ↔
      seqDef.val.Evalb ![h] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![n,h] Empty.elim ∘ traceSeqRew ∘ Semiterm.bvar) = ![h] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have he : (Semiterm.val (L := language) ![n,h] Empty.elim ∘ traceSeqRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem traceLh_eval (n h : M) :
    (traceLhRew ▹ Semiformula.lMap embedding lhDef.val).Eval ![n,h] Empty.elim ↔
      lhDef.val.Evalb ![n+1,h] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![n,h] Empty.elim ∘ traceLhRew ∘ Semiterm.bvar) = ![n+1,h] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) addCode
        (Semiterm.val (L := language) ![n,h] Empty.elim ∘ ![#0,.func oneCode Fin.elim0]) = _
      congr 1
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      change Structure.func (L := language) oneCode
        (Semiterm.val (L := language) ![n,h] Empty.elim ∘ Fin.elim0) = _
      congr 1
      exact Subsingleton.elim _ _
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have he : (Semiterm.val (L := language) ![n,h] Empty.elim ∘ traceLhRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem traceMem_eval (value : Code 1) (i n h : M) :
    (traceMemRew value ▹ Semiformula.lMap embedding memRel.val).Eval ![i,n,h] Empty.elim ↔
      memRel.val.Evalb ![h,i,Structure.func (L := language) value (fun _ => i)] := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![i,n,h] Empty.elim ∘ traceMemRew value ∘ Semiterm.bvar) =
      ![h,i,Structure.func (L := language) value (fun _ => i)] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change Structure.func (L := language) value
      (Semiterm.val (L := language) ![i,n,h] Empty.elim ∘ ![#0]) = _
    congr 1
    funext k
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![i,n,h] Empty.elim ∘ traceMemRew value ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
theorem trace_eval (value : Code 1) (n h : M) : (traceMatrix value).Eval ![n,h] Empty.elim ↔
    seqDef.val.Evalb ![h] ∧ lhDef.val.Evalb ![n+1,h] ∧
      ∀ i < n+1, memRel.val.Evalb ![h,i,Structure.func (L := language) value (fun _ => i)] := by
  have hz (x : M) : (Semiterm.val (L := language) ![x,n,h] Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [traceMatrix, FirstOrder.ball, traceSeq_eval, traceLh_eval, traceMem_eval,
    Semiformula.eval_rel, Semiterm.val_func, hz]
  intro _ _
  rfl


omit [Structure.Eq language M] in
theorem modelSeqCons (cons : Code 2) (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (s x : M) :
    (Semiformula.lMap embedding seqConsDef.val).Eval
      ![Structure.func (L := language) cons ![s,x],s,x] Empty.elim := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcons
  simp only [models_iff, PRAHistorySeqConsCode.graphSentence, Semiformula.eval_allClosure] at hm
  have hm := hm ![s,x]
  simp only [Semiformula.eval_rew] at hm
  have hv : (Semiterm.val (L := language) ![s,x] Empty.elim ∘
      PRAHistorySeqConsCode.graphRew cons ∘ Semiterm.bvar) =
      ![Structure.func (L := language) cons ![s,x],s,x] := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change Structure.func (L := language) cons
        (Semiterm.val (L := language) ![s,x] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have he : (Semiterm.val (L := language) ![s,x] Empty.elim ∘
      PRAHistorySeqConsCode.graphRew cons ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he] at hm
  exact hm

set_option maxHeartbeats 3000000 in
theorem modelTraceBase (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
      rw [PRAModelIOpenPairing.reduct_eq_standard] at h
      exact h
    (traceMatrix (valueCode base step)).Eval
      ![(0 : M),Structure.func (L := language) (firstHistory cons base) Fin.elim0] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  let x : M := Structure.func (L := language) base Fin.elim0
  let h : M := Structure.func (L := language) (firstHistory cons base) Fin.elim0
  have hh : h = Structure.func (L := language) cons ![(0 : M),x] := by
    dsimp only [h,x,firstHistory]
    rw [PRAHistoryPairCode.modelBin]
    rfl
  have hc := modelSeqCons cons hcons 0 x
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hc
  have hgraph : seqConsDef.val.Evalb ![h,0,x] := by rw [hh]; exact hc
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hseq,hlh⟩ := PRAHistorySingletonSequence.singleton_sequence hexp h x hgraph
  rw [trace_eval]
  refine ⟨hseq,by simpa using hlh,?_⟩
  intro i hi
  have hi0 : i = 0 := by
    have : i ≤ 0 := lt_succ_iff_le.mp (by simpa using hi)
    exact le_antisymm this (by simp)
  have hm := PRAHistorySingletonMembership.singleton_memRel hexp h x hgraph i
    (Structure.func (L := language) (valueCode base step) (fun _ => i))
  apply hm.mpr
  refine ⟨hi0,?_⟩
  rw [hi0]
  change Structure.func (L := language) (valueCode base step)
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) = x
  rw [modelValueBase]
theorem modelHistoryStepValue (cons : Code 2) (base : Code 0) (step : Code 2) (n h : M) :
    Structure.func (L := language) (historyStep cons base step) ![n,h] =
      Structure.func (L := language) cons ![h,
        Structure.func (L := language) (valueCode base step)
          (fun _ => Structure.func (L := language) Code.succ (fun _ => n))] := by
  rw [historyStep,PRAHistoryPairCode.modelBin,modelProjection,nextValue,modelComposition]
  congr 1
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases ?_ (fun l => Fin.elim0 l) k
  have ha : (fun j : Fin 1 => Structure.func (L := language)
      (getCode (.cons nextIndex (.nil 2)) j) ![n,h]) =
      (fun _ => Structure.func (L := language) Code.succ (fun _ => n)) := by
    funext j
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) nextIndex ![n,h] = _
    rw [nextIndex,modelComposition]
    congr 1
    funext k
    refine Fin.cases ?_ (fun l => Fin.elim0 l) k
    exact modelProjection 0 _
  rw [ha]
  rfl

set_option maxHeartbeats 3000000 in
theorem modelTraceStep (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n h : M)
    (htrace : (traceMatrix (valueCode base step)).Eval ![n,h] Empty.elim) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
      rw [PRAModelIOpenPairing.reduct_eq_standard] at h
      exact h
    (traceMatrix (valueCode base step)).Eval
      ![Structure.func (L := language) Code.succ (fun _ => n),
        Structure.func (L := language) (historyStep cons base step) ![n,h]] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  let x : M := Structure.func (L := language) (valueCode base step)
    (fun _ => Structure.func (L := language) Code.succ (fun _ => n))
  let t : M := Structure.func (L := language) cons ![h,x]
  have hc := modelSeqCons cons hcons h x
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hc
  have hgraph : seqConsDef.val.Evalb ![t,h,x] := hc
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hseq,hlh,hmem⟩ := (trace_eval _ n h).mp htrace
  have hs := PRAHistoryLengthUnique.modelAppendLength t h x (n+1) hseq hlh hgraph
  obtain ⟨l,_,hld,hm⟩ := PRAHistorySeqConsMembership.seqCons_membership hexp t h x hgraph
  have heq : l = n+1 := PRAHistoryLengthUnique.modelLengthUnique h l (n+1) hld hlh
  rw [heq] at hm
  rw [modelHistoryStepValue]
  change (traceMatrix (valueCode base step)).Eval
    ![Structure.func (L := language) Code.succ (fun _ => n),t] Empty.elim
  rw [←modelAddOne]
  change (traceMatrix (valueCode base step)).Eval ![n+1,t] Empty.elim
  apply (trace_eval _ (n+1) t).mpr
  refine ⟨hs.1,by simpa [add_assoc] using hs.2,?_⟩
  intro i hi
  have hi' : i ≤ n+1 := lt_succ_iff_le.mp (by simpa [add_assoc] using hi)
  rcases le_iff_lt_or_eq.mp hi' with hlt | heq'
  · exact (hm i _).mpr (Or.inr (hmem i hlt))
  · have hx : Structure.func (L := language) (valueCode base step) (fun _ => i) = x := by
      rw [heq']
      dsimp only [x]
      rw [←modelAddOne]
      rfl
    exact (hm i _).mpr (Or.inl ⟨heq',hx⟩)
set_option maxHeartbeats 3000000 in
theorem modelTraceHistory (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n : M) :
    (traceMatrix (valueCode base step)).Eval
      ![n,Structure.func (L := language) (historyCode cons base step) (fun _ => n)] Empty.elim := by
  obtain ⟨pred,_,_,hpred⟩ := PRA_proves_boundedBooleanCharacteristic
    (traceMatrix (valueCode base step)) (traceMatrix_bounded _)
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hpred
  have hc := (oneCorrectSentence_iff pred (traceMatrix (valueCode base step))).mp hm
  let e : ℕ → M := fun _ => n
  have he : (fun _ : Fin 0 => n) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hbase : Structure.func (L := language) pred
      (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases (Structure.func (L := language) (firstHistory cons base) (fun i : Fin 0 => e i.val))
          (fun i : Fin 0 => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
    rw [he]
    change Structure.func (L := language) pred
      ![(0 : M),Structure.func (L := language) (firstHistory cons base) Fin.elim0] = _
    exact (hc _).mpr (modelTraceBase cons base step hcons)
  have hstep : ∀ x y : M, Structure.func (L := language) pred
      (Fin.cases x (Fin.cases y (fun i : Fin 0 => e i.val))) =
        Structure.func (L := language) oneCode Fin.elim0 →
      Structure.func (L := language) pred
        (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
          (Fin.cases (Structure.func (L := language) (historyStep cons base step)
            (Fin.cases x (Fin.cases y (fun i : Fin 0 => e i.val))))
            (fun i : Fin 0 => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
    intro x y hy
    rw [he] at hy ⊢
    change Structure.func (L := language) pred ![x,y] = _ at hy
    change Structure.func (L := language) pred
      ![Structure.func (L := language) Code.succ (fun _ => x),
        Structure.func (L := language) (historyStep cons base step) ![x,y]] = _
    apply (hc _).mpr
    exact modelTraceStep cons base step hcons x y ((hc ![x,y]).mp hy)
  have h := PRAPrimitiveRecursionInduction.modelRecursiveWitness (M := M) pred
    (firstHistory cons base) (historyStep cons base step) e hbase hstep n
  rw [he] at h
  have hv : Fin.cases n (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => n) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv] at h
  change Structure.func (L := language) pred
    ![n,Structure.func (L := language) (historyCode cons base step) (fun _ => n)] = _ at h
  exact (hc _).mp h
def traceRew (cons : Code 2) (base : Code 0) (step : Code 2) : Rew language Empty 2 Empty 1 :=
  Rew.embSubsts ![#0,.func (historyCode cons base step) ![#0]]

def traceSentence (cons : Code 2) (base : Code 0) (step : Code 2) : Sentence language := ∀⁰*
  (traceRew cons base step ▹ traceMatrix (valueCode base step))

theorem modelTraceSentence (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) :
    M↓[language] ⊧ traceSentence cons base step := by
  simp only [models_iff,traceSentence,Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_one e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0] Empty.elim ∘ traceRew cons base step ∘ Semiterm.bvar) =
      ![e 0,Structure.func (L := language) (historyCode cons base step) (fun _ => e 0)] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) (historyCode cons base step)
      (Semiterm.val (L := language) ![e 0] Empty.elim ∘ ![#0]) = _
    congr 1
    funext k
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0] Empty.elim ∘ traceRew cons base step ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelTraceHistory cons base step hcons (e 0)
end models

theorem PRA_proves_trace (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) : PRA ⊢ traceSentence cons base step := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelTraceSentence cons base step hcons

theorem PRA_has_trace (base : Code 0) (step : Code 2) :
    ∃ cons : Code 2, PRA ⊢ PRAHistorySeqConsCode.graphSentence cons ∧ PRA ⊢ traceSentence cons base step := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  exact ⟨cons,hcons,PRA_proves_trace cons base step hcons⟩
end DiophantineConsistency.PRAHistoryTrace
