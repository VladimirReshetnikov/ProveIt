import PA196PRAQVecTowerCSeq

/-! A bounded predicate for comparing an arbitrary arithmetic tower CSeq
with the candidate-PRA tower at its model-internal indices. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PRAQVecTowerCSeqInduction
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
  PRABoundedCharacteristic PRABoundedWitness PRABoundedFormula
open PA196PRAQVecTower PA196PRAQVecStepMonotone PA196PRAQVecTowerCSeq PA196PAQVecSeqTrace

noncomputable def entryRew : Rew language Empty 3 Empty 4 :=
  Rew.embSubsts ![#2,#0,.func towerCode ![#0,#3]]
noncomputable def entryMatrix : Semisentence language 4 :=
  (∼(Semiformula.rel Language.ORing.Rel.lt ![#0,#1])) ⋎
    (entryRew ▹ Semiformula.lMap embedding memRel.val)

theorem entryMatrix_bounded : Hierarchy 𝚺 0 entryMatrix := by
  unfold entryMatrix
  apply Hierarchy.or
  · exact Hierarchy.nrel _ _ _ _
  · exact Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy memRel.sigma_prop)

def inductionBody (pred : Code 4) : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func pred ![#0,&0,&1,&2],.func oneCode Fin.elim0]
theorem inductionBody_open (pred : Code 4) : (inductionBody pred).Open := by
  simp [inductionBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem entryMatrix_eval (i l s seed : M) :
    entryMatrix.Eval ![i,l,s,seed] Empty.elim ↔
      (i < l → memRel.val.Evalb ![s,i,tower i seed]) := by
  have hv : (Semiterm.val (L := language) ![i,l,s,seed] Empty.elim ∘ entryRew ∘ Semiterm.bvar) =
      ![s,i,tower i seed] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases ?_ (fun k => Fin.elim0 k) k
    change Structure.func (L := language) towerCode
      (Semiterm.val (L := language) ![i,l,s,seed] Empty.elim ∘ ![#0,#3]) = _
    congr 1
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    exact Fin.cases rfl (fun t => Fin.elim0 t) j
  have he : (Semiterm.val (L := language) ![i,l,s,seed] Empty.elim ∘ entryRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp only [entryMatrix, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    Semiformula.eval_rel, Semiformula.eval_rew]
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  have ha : (Semiterm.val (L := language) ![i,l,s,seed] Empty.elim ∘
      (![#0,#1] : Fin 2 → Semiterm language Empty 4)) = ![i,l] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun a => Fin.elim0 a) k) j
  rw [ha]
  change (¬Structure.rel (L := language) Language.ORing.Rel.lt ![i,l] ∨
    memRel.val.Evalb ![s,i,tower i seed]) ↔
      (Structure.rel (L := language) Language.ORing.Rel.lt ![i,l] →
        memRel.val.Evalb ![s,i,tower i seed])
  constructor
  · rintro (hn | hm) hi
    · exact (hn hi).elim
    · exact hm
  · intro h
    by_cases hi : Structure.rel (L := language) Language.ORing.Rel.lt ![i,l]
    · exact Or.inr (h hi)
    · exact Or.inl hi

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem inductionBody_eval (pred : Code 4) (i : M) (e : ℕ → M) :
    (inductionBody pred).Eval ![i] e ↔
      Structure.func (L := language) pred ![i,e 0,e 1,e 2] =
        Structure.func (L := language) oneCode Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![i] (inductionBody pred) ↔ _
  dsimp only [inductionBody, Semiformula.EvalAux]
  rw [eqRel]
  have he : (Semiterm.val (L := language) ![i] e ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiterm.val_func, he]
/-- Every entry below the length agrees with the candidate tower. The
induction is over a bounded characteristic predicate in candidate PRA. -/
theorem cseq_entries (s seed l : M) (hs : boundBlueprint.cseqDef.val.Evalb ![s,seed])
    (hl : l ≤ 2*s) (hld : lhDef.val.Evalb ![l,s]) :
    ∀ i < l, memRel.val.Evalb ![s,i,tower i seed] := by
  obtain ⟨_,hzero,hsucc⟩ := (cseq_spec s seed).mp hs
  obtain ⟨z,hz,hzseed,hzero⟩ := hzero
  subst z
  obtain ⟨pred,_,_,hpred⟩ := PRA_proves_boundedBooleanCharacteristic
    entryMatrix entryMatrix_bounded
  have hmodel := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hpred
  have hc := (oneCorrectSentence_iff pred entryMatrix).mp hmodel
  let e : ℕ → M := fun n => if n = 0 then l else if n = 1 then s else seed
  have hexp (x : M) : ∃ y, Exponential x y := ⟨_,PRAHistoryTruncation.exponential_expF x⟩
  intro i hi
  have hI := modelOpenInduction (M := M) (inductionBody pred) (inductionBody_open pred) e
    (by
      apply (inductionBody_eval pred 0 e).mpr
      apply (hc _).mpr
      apply (entryMatrix_eval 0 l s seed).mpr
      intro _
      simpa [tower_zero] using hzero)
    (by
      intro t ht
      apply (inductionBody_eval pred (Structure.func (L := language) Code.succ (fun _ => t)) e).mpr
      apply (hc _).mpr
      rw [show Structure.func (L := language) Code.succ (fun _ => t) = t+1 from (modelAddOne t).symm]
      apply (entryMatrix_eval (t+1) l s seed).mpr
      intro ht1
      have htlt : t < l := lt_of_lt_of_le (lt_add_one t) (le_of_lt ht1)
      have hprev : memRel.val.Evalb ![s,t,tower t seed] := by
        have h := (hc ![t,l,s,seed]).mp ((inductionBody_eval pred t e).mp ht)
        exact (entryMatrix_eval t l s seed).mp h htlt
      have hz : tower t seed < s := PRAHistoryDomainExtension.memRel_value_lt hexp hprev
      have hti : t < 2*s := lt_of_lt_of_le htlt hl
      obtain ⟨u,_,hu,hm⟩ := hsucc t hti ⟨l,hl,hld,ht1⟩ (tower t seed) hz hprev
      rw [hu] at hm
      simpa [tower_succ_majorant] using hm) i
  have h := (hc ![i,l,s,seed]).mp ((inductionBody_eval pred i e).mp hI)
  exact (entryMatrix_eval i l s seed).mp h hi
end models
#print axioms cseq_entries
#print axioms entryMatrix_bounded
#print axioms entryMatrix_eval
end PA196PRAQVecTowerCSeqInduction
