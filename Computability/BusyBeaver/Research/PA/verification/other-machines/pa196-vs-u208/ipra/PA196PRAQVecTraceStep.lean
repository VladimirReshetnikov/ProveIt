import PA196PRAQVecTraceMatrix

/-! The bounded tower-trace predicate is preserved by the candidate-PRA
history constructor for arbitrary parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA196PRAQVecTraceStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PA196PRAQVecTower PA196PRAQVecHistory PA196PRAQVecTraceMatrix

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem historyStepValue (cons : Code 2) (n h seed : M) :
    Structure.func (L := language) (historyStep cons) ![n,h,seed] =
      Structure.func (L := language) cons ![h,tower (n+1) seed] := by
  rw [historyStep,modelBin,modelProjection,nextValue,modelComposition]
  congr 1
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases ?_ (fun l => Fin.elim0 l) k
  change Structure.func (L := language) towerCode _ = tower (n+1) seed
  unfold tower
  congr 1
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · change Structure.func (L := language) nextIndex ![n,h,seed] = n+1
    rw [nextIndex, modelComposition]
    calc
      _ = Structure.func (L := language) Code.succ (fun _ => n) := by
        congr 1
        funext j
        refine Fin.cases ?_ (fun k => Fin.elim0 k) j
        exact modelProjection 0 _
      _ = n + 1 := (modelAddOne n).symm
  · exact Fin.cases (modelProjection 2 _) (fun m => Fin.elim0 m) l

theorem traceBase (cons : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (seed : M) :
    traceMatrix.Eval ![(0 : M),Structure.func (L := language) (firstHistory cons) ![seed],seed] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  let h : M := Structure.func (L := language) (firstHistory cons) ![seed]
  have hh : h = Structure.func (L := language) cons ![(0 : M),seed] := by
    dsimp only [h,firstHistory]
    rw [modelBin, modelProjection, PRAMultiplication.modelZero]
    rfl
  have hc := PRAHistoryTrace.modelSeqCons cons hcons 0 seed
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hc
  have hgraph : seqConsDef.val.Evalb ![h,0,seed] := by rw [hh]; exact hc
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hseq,hlh⟩ := PRAHistorySingletonSequence.singleton_sequence hexp h seed hgraph
  change traceMatrix.Eval ![(0 : M),h,seed] Empty.elim
  rw [trace_eval]
  refine ⟨hseq,by simpa using hlh,?_⟩
  intro i hi
  have hi0 : i = 0 := by
    have : i ≤ 0 := lt_succ_iff_le.mp (by simpa using hi)
    exact le_antisymm this (by simp)
  have hm := PRAHistorySingletonMembership.singleton_memRel hexp h seed hgraph i (tower i seed)
  apply hm.mpr
  refine ⟨hi0,?_⟩
  rw [hi0, tower_zero]

theorem traceStep (cons : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n h seed : M)
    (htrace : traceMatrix.Eval ![n,h,seed] Empty.elim) :
    traceMatrix.Eval ![Structure.func (L := language) Code.succ (fun _ => n),
      Structure.func (L := language) (historyStep cons) ![n,h,seed],seed] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  let x : M := tower (n+1) seed
  let t : M := Structure.func (L := language) cons ![h,x]
  have hc := PRAHistoryTrace.modelSeqCons cons hcons h x
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hc
  have hgraph : seqConsDef.val.Evalb ![t,h,x] := hc
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  obtain ⟨hseq,hlh,hmem⟩ := (trace_eval n h seed).mp htrace
  have hs := PRAHistoryLengthUnique.modelAppendLength t h x (n+1) hseq hlh hgraph
  obtain ⟨l,_,hld,hm⟩ := PRAHistorySeqConsMembership.seqCons_membership hexp t h x hgraph
  have heq : l = n+1 := PRAHistoryLengthUnique.modelLengthUnique h l (n+1) hld hlh
  rw [heq] at hm
  rw [historyStepValue]
  change traceMatrix.Eval ![Structure.func (L := language) Code.succ (fun _ => n),t,seed] Empty.elim
  rw [←modelAddOne]
  change traceMatrix.Eval ![n+1,t,seed] Empty.elim
  apply (trace_eval (n+1) t seed).mpr
  refine ⟨hs.1,by simpa [add_assoc] using hs.2,?_⟩
  intro i hi
  have hi' : i ≤ n+1 := lt_succ_iff_le.mp (by simpa [add_assoc] using hi)
  rcases le_iff_lt_or_eq.mp hi' with hlt | heq'
  · exact (hm i _).mpr (Or.inr (hmem i hlt))
  · have hx : tower i seed = x := by rw [heq']
    exact (hm i _).mpr (Or.inl ⟨heq',hx⟩)
end models
#print axioms historyStepValue
#print axioms traceBase
#print axioms traceStep
end PA196PRAQVecTraceStep
