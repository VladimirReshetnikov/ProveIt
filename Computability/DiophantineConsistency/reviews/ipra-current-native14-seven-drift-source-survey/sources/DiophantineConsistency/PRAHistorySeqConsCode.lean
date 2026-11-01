import DiophantineConsistency.PRAHistoryLengthCode
import DiophantineConsistency.PRAHistoryInsertCode
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySeqConsCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAHistoryLengthCode PRAHistoryInsertCode PRAHerbrandSelection

def seqConsCode (len : Code 1) (ins : Code 2) : Code 2 :=
  bin ins (bin pairCode (.comp len (.cons (.proj 0) (.nil 2))) (.proj 1)) (.proj 0)

set_option maxHeartbeats 2000000 in
theorem seqCons_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (t s x : V) :
    seqConsDef.val.Evalb ![t,s,x] ↔ ∃ l ≤ 2*s, lhDef.val.Evalb ![l,s] ∧
      ∃ p ≤ (2*s+x+1)^2, pairDef.val.Evalb ![p,l,x] ∧ insertDef.val.Evalb ![t,p,s] := by
  simp [seqConsDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelLength (len : Code 1) (h : PRA ⊢ (∀⁰* openMatrixAt mappedMatrix len)) (s : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
    Structure.func (L := language) len (fun _ => s) ≤ 2*s ∧
      lhDef.val.Evalb ![Structure.func (L := language) len (fun _ => s),s] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, Semiformula.eval_allClosure] at hm
  have hm := hm ![s]
  rw [openMatrixAt, Semiformula.eval_substs] at hm
  have hv : (Semiterm.val (L := language) ![s] Empty.elim ∘
      Fin.cases (applyCode len (vars 1)) (vars 1)) =
      ![Structure.func (L := language) len (fun _ => s),s] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) len
        (Semiterm.val (L := language) ![s] Empty.elim ∘ vars 1) = _
      congr 1
      funext j
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv,mappedMatrix, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hm
  simpa [lhMatrix, Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq,
    lt_succ_iff_le] using hm

omit [Structure.Eq language M] in
theorem modelInsert (ins : Code 2) (h : PRA ⊢ PRAHistoryInsertCode.graphSentence ins) (i s : M) :
    (Semiformula.lMap embedding insertDef.val).Eval
      ![Structure.func (L := language) ins ![i,s],i,s] Empty.elim := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, PRAHistoryInsertCode.graphSentence, Semiformula.eval_allClosure] at hm
  have hm := hm ![i,s]
  simp only [Semiformula.eval_rew] at hm
  have hv : (Semiterm.val (L := language) ![i,s] Empty.elim ∘
      PRAHistoryInsertCode.graphRew ins ∘ Semiterm.bvar) =
      ![Structure.func (L := language) ins ![i,s],i,s] := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change Structure.func (L := language) ins
        (Semiterm.val (L := language) ![i,s] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have he : (Semiterm.val (L := language) ![i,s] Empty.elim ∘
      PRAHistoryInsertCode.graphRew ins ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he] at hm
  exact hm

theorem modelSeqConsCode (len : Code 1) (ins : Code 2)
    (hlen : PRA ⊢ (∀⁰* openMatrixAt mappedMatrix len))
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins) (s x : M) :
    (Semiformula.lMap embedding seqConsDef.val).Eval
      ![Structure.func (L := language) (seqConsCode len ins) ![s,x],s,x] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  let l := Structure.func (L := language) len (fun _ => s)
  let p := pair l x
  have hl := modelLength len hlen s
  have hpbound : p ≤ (2*s+x+1)^2 := by
    exact le_trans (pair_le_pair_left hl.1 x) (pair_polybound (2*s) x)
  have hpgraph : pairDef.val.Evalb ![p,l,x] := by
    have h := (PRAModelIOpenPairing.pairGraph_spec l x p).mpr rfl
    rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  have hinsgraph : insertDef.val.Evalb
      ![Structure.func (L := language) ins ![p,s],p,s] := by
    have h := modelInsert ins hins p s
    rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  have hval : Structure.func (L := language) (seqConsCode len ins) ![s,x] =
      Structure.func (L := language) ins ![p,s] := by
    rw [seqConsCode, modelBin, modelBin]
    simp only [modelProjection]
    have he : Structure.func (L := language)
        (Code.comp len (.cons (.proj 0) (.nil 2))) ![s,x] = l := by
      rw [modelComposition]
      congr 1
      funext j
      refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      exact modelProjection 0 ![s,x]
    rw [he]
    rw [modelPairCode]
    rfl
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard, seqCons_iff, hval]
  exact ⟨l,hl.1,hl.2,p,hpbound,hpgraph,hinsgraph⟩
def graphRew (c : Code 2) : Rew language Empty 3 Empty 2 := Rew.embSubsts
  ![.func c ![#0,#1],#0,#1]

def graphSentence (c : Code 2) : Sentence language := ∀⁰*
  (graphRew c ▹ Semiformula.lMap embedding seqConsDef.val)

theorem modelGraphSentence (len : Code 1) (ins : Code 2)
    (hlen : PRA ⊢ (∀⁰* openMatrixAt mappedMatrix len))
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins) :
    M↓[language] ⊧ graphSentence (seqConsCode len ins) := by
  simp only [models_iff, graphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      graphRew (seqConsCode len ins) ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (seqConsCode len ins) ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (seqConsCode len ins)
        (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      graphRew (seqConsCode len ins) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelSeqConsCode len ins hlen hins (e 0) (e 1)
end models

theorem PRA_has_seqConsCode : ∃ c : Code 2, PRA ⊢ graphSentence c := by
  obtain ⟨len,_,hlen⟩ := PRA_has_lengthCode
  obtain ⟨ins,hins⟩ := PRA_has_insertCode
  refine ⟨seqConsCode len ins, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelGraphSentence len ins hlen hins
end DiophantineConsistency.PRAHistorySeqConsCode
