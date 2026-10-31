import DiophantineConsistency.PRAHistoryTrace
import Foundation.FirstOrder.Arithmetic.HFS.PRF
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryResultGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryIterator PRAHistoryTrace

set_option maxHeartbeats 3000000 in
theorem seq_rel_unique {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (s i a b : V)
    (hs : seqDef.val.Evalb ![s]) (ha : memRel.val.Evalb ![s,i,a])
    (hb : memRel.val.Evalb ![s,i,b]) : a = b := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hm : isMappingDef.val.Evalb ![s] := by
    have h := hs
    simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le] at h
    exact h.1
  obtain ⟨d,_,hdom,hmap⟩ := (PRAHistorySequenceExtension.mapping_iff hexp s).mp hm
  have had : bitDef.val.Evalb ![i,d] :=
    ((PRAHistoryDomainExtension.domain_iff hexp d s).mp hdom i).mpr
      ⟨a,PRAHistoryDomainExtension.memRel_value_lt hexp ha,ha⟩
  obtain ⟨y,_,hy,hyuniq⟩ := hmap i had
  have ea := hyuniq a (PRAHistoryDomainExtension.memRel_value_lt hexp ha) ha
  have eb := hyuniq b (PRAHistoryDomainExtension.memRel_value_lt hexp hb) hb
  exact ea.trans eb.symm

set_option maxHeartbeats 3000000 in
theorem cseq_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (B : PR.Blueprint 0) (h : V) : B.cseqDef.val.Evalb ![h] ↔
      seqDef.val.Evalb ![h] ∧
      (∃ z < h, B.zero.val.Evalb ![z] ∧ memRel.val.Evalb ![h,0,z]) ∧
      ∀ i < 2*h, (∃ l ≤ 2*h, lhDef.val.Evalb ![l,h] ∧ i+1 < l) →
        ∀ z < h, memRel.val.Evalb ![h,i,z] →
          ∃ u < h, B.succ.val.Evalb ![u,z,i] ∧ memRel.val.Evalb ![h,i+1,u] := by
  simp [PR.Blueprint.cseqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    Semiformula.ballLT, FirstOrder.bexs, FirstOrder.ball, Semiformula.Operator.val,
    memRelOpr, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]

def zeroGraphRew (base : Code 0) : Rew language Empty 1 Empty 0 :=
  Rew.embSubsts ![.func base Fin.elim0]
noncomputable def zeroGraphSentence (B : PR.Blueprint 0) (base : Code 0) : Sentence language :=
  zeroGraphRew base ▹ Semiformula.lMap embedding B.zero.val

def stepGraphRew (step : Code 2) : Rew language Empty 3 Empty 2 :=
  Rew.embSubsts ![.func step ![#0,#1],#1,#0]
noncomputable def stepGraphSentence (B : PR.Blueprint 0) (step : Code 2) : Sentence language := ∀⁰*
  (stepGraphRew step ▹ Semiformula.lMap embedding B.succ.val)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

set_option maxHeartbeats 3000000 in
theorem modelCseqFromTrace (B : PR.Blueprint 0) (base : Code 0) (step : Code 2) (n h : M)
    (htrace : (traceMatrix (valueCode base step)).Eval ![n,h] Empty.elim)
    (hzero : B.zero.val.Evalb ![Structure.func (L := language) (M := M) base Fin.elim0])
    (hstep : ∀ i z : M, B.succ.val.Evalb ![Structure.func (L := language) step ![i,z],z,i]) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have hh := PRAModelISigmaZero.modelReductISigmaZero (M := M)
      rw [PRAModelIOpenPairing.reduct_eq_standard] at hh
      exact hh
    B.cseqDef.val.Evalb ![h] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have hh := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at hh
    exact hh
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hs,hl,hmem⟩ := (trace_eval _ n h).mp htrace
  apply (cseq_iff B h).mpr
  refine ⟨hs,?_,?_⟩
  · have hm := hmem 0 (by simp)
    have hv : Structure.func (L := language) (valueCode base step) (fun _ => (0 : M)) =
        Structure.func (L := language) base Fin.elim0 := by
      change Structure.func (L := language) (valueCode base step)
        (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) = _
      exact modelValueBase base step
    rw [hv] at hm
    exact ⟨_,PRAHistoryDomainExtension.memRel_value_lt hexp hm,hzero,hm⟩
  · intro i _ ⟨l,_,hld,hi⟩ z _ hz
    have hlEq : l = n+1 := PRAHistoryLengthUnique.modelLengthUnique h l (n+1) hld hl
    rw [hlEq] at hi
    have hin : i < n+1 := lt_of_le_of_lt (by simp) hi
    have hm := hmem i hin
    have hzEq : z = Structure.func (L := language) (valueCode base step) (fun _ => i) :=
      seq_rel_unique hexp h i z _ hs hz hm
    have hmNext := hmem (i+1) hi
    let u := Structure.func (L := language) (valueCode base step) (fun _ => i+1)
    have hsucc := hstep i (Structure.func (L := language) (valueCode base step) (fun _ => i))
    have hv : u = Structure.func (L := language) step
        ![i,Structure.func (L := language) (valueCode base step) (fun _ => i)] := by
      dsimp only [u]
      change Structure.func (L := language) (valueCode base step)
        (fun _ => Structure.func (L := language) addCode ![i,Structure.func (L := language) oneCode Fin.elim0]) = _
      rw [modelAddOne]
      exact modelValueStep base step i
    rw [←hv,←hzEq] at hsucc
    exact ⟨u,PRAHistoryDomainExtension.memRel_value_lt hexp hmNext,hsucc,hmNext⟩

theorem modelZeroGraph (B : PR.Blueprint 0) (base : Code 0)
    (hz : PRA ⊢ zeroGraphSentence B base) :
    B.zero.val.Evalb ![Structure.func (L := language) (M := M) base Fin.elim0] := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hz
  simp only [models_iff,zeroGraphSentence,Semiformula.eval_rew] at hm
  have hv : (Semiterm.val (L := language) ![] Empty.elim ∘ zeroGraphRew base ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (M := M) base Fin.elim0] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) base
      (Semiterm.val (L := language) ![] Empty.elim ∘ Fin.elim0) = _
    congr 1
    exact Subsingleton.elim _ _
  have he : (Semiterm.val (L := language) ![] Empty.elim ∘ zeroGraphRew base ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hm
  exact hm

theorem modelStepGraph (B : PR.Blueprint 0) (step : Code 2)
    (hs : PRA ⊢ stepGraphSentence B step) (i z : M) :
    B.succ.val.Evalb ![Structure.func (L := language) step ![i,z],z,i] := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hs
  simp only [models_iff,stepGraphSentence,Semiformula.eval_allClosure] at hm
  have hm := hm ![i,z]
  simp only [Semiformula.eval_rew] at hm
  have hv : (Semiterm.val (L := language) ![i,z] Empty.elim ∘ stepGraphRew step ∘ Semiterm.bvar) =
      ![Structure.func (L := language) step ![i,z],z,i] := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change Structure.func (L := language) step
        (Semiterm.val (L := language) ![i,z] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have he : (Semiterm.val (L := language) ![i,z] Empty.elim ∘ stepGraphRew step ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hm
  exact hm

set_option maxHeartbeats 3000000 in
theorem modelResultFromTrace (B : PR.Blueprint 0) (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons)
    (hz : PRA ⊢ zeroGraphSentence B base) (hs : PRA ⊢ stepGraphSentence B step) (n : M) :
    B.resultDef.val.Evalb ![Structure.func (L := language) (valueCode base step) (fun _ => n),n] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have hh := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at hh
    exact hh
  let h := Structure.func (L := language) (historyCode cons base step) (fun _ => n)
  have ht := modelTraceHistory cons base step hcons n
  have hc := modelCseqFromTrace B base step n h ht (modelZeroGraph B base hz) (modelStepGraph B step hs)
  obtain ⟨_,_,hm⟩ := (trace_eval _ n h).mp ht
  have hmem := hm n (by simp)
  simp [PR.Blueprint.resultDef, Semiformula.Operator.val, memRelOpr]
  exact ⟨h,hc,hmem⟩

def resultGraphRew (base : Code 0) (step : Code 2) : Rew language Empty 2 Empty 1 :=
  Rew.embSubsts ![.func (valueCode base step) ![#0],#0]
noncomputable def resultGraphSentence (B : PR.Blueprint 0) (base : Code 0) (step : Code 2) : Sentence language := ∀⁰*
  (resultGraphRew base step ▹ Semiformula.lMap embedding B.resultDef.val)

theorem modelResultSentence (B : PR.Blueprint 0) (cons : Code 2) (base : Code 0) (step : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons)
    (hz : PRA ⊢ zeroGraphSentence B base) (hs : PRA ⊢ stepGraphSentence B step) :
    M↓[language] ⊧ resultGraphSentence B base step := by
  simp only [models_iff,resultGraphSentence,Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_one e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0] Empty.elim ∘ resultGraphRew base step ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (valueCode base step) (fun _ => e 0),e 0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (valueCode base step)
        (Semiterm.val (L := language) ![e 0] Empty.elim ∘ ![#0]) = _
      congr 1
      funext k
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have he : (Semiterm.val (L := language) ![e 0] Empty.elim ∘ resultGraphRew base step ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  exact modelResultFromTrace B cons base step hcons hz hs (e 0)
end models

theorem PRA_proves_resultGraph (B : PR.Blueprint 0) (base : Code 0) (step : Code 2)
    (hz : PRA ⊢ zeroGraphSentence B base) (hs : PRA ⊢ stepGraphSentence B step) :
    PRA ⊢ resultGraphSentence B base step := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelResultSentence B cons base step hcons hz hs
end DiophantineConsistency.PRAHistoryResultGraph
