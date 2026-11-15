import PA194ModelQuantifierFreeFresh
import PA194PAeqBooleanCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqQFCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Entailment Classical PA194ModelLogic PA194PAeqTermBlueprint PA194PAeq.AtomicCongruence PA194PAeq.BooleanCongruence
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance qfPAeqZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfPAeqOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfPAeqAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfPAeqMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfPAeqLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfPAeqIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






noncomputable local instance : PA194PAeq.ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem self_imp (p : M) (hp : IsSemiformula PA194PAeq.language 0 p) :
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language p p) := by
  let T : InternalTheory M PA194PAeq.language := ⟨PA194PAeq.ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula M PA194PAeq.language := ⟨p,hp⟩
  have h : T ⊢ P 🡒 P := C!_id
  have h' := (TProvable.iff_provable).mp h
  simpa [T,P,Semiformula.imp_def,imp] using h'

theorem replace (p a b : M) (hp : IsSemiformula PA194PAeq.language 1 p) (hqf : InternalQuantifierFree p)
    (ha : IsSemiterm PA194PAeq.language 0 a) (hb : IsSemiterm PA194PAeq.language 0 b)
    (hab : Provable PA194PAeq.ordinaryPAeq (equalityCode a b)) :
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language (substs1 PA194PAeq.language a p) (substs1 PA194PAeq.language b p)) := by
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q → IsSemiformula PA194PAeq.language 1 q →
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language (substs1 PA194PAeq.language a q) (substs1 PA194PAeq.language b q))) := by
    definability
  have hall : ∀ q, IsUFormula PA194PAeq.language q → InternalQuantifierFree q → IsSemiformula PA194PAeq.language 1 q →
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language (substs1 PA194PAeq.language a q) (substs1 PA194PAeq.language b q)) := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv hqf hscope
      obtain ⟨rfl,rfl⟩ := (PA194PAeq.source_relations arity r).mp hr
      obtain ⟨x,y,hx,hy,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hs,ht⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      have h := atomic_replace ha hb hs ht hab
      simpa [substs1,PA194PAeqTermBlueprint.equalityCode,PA194PAeq.source_relations,hx,hy] using h
    · intro arity r v hr hv hqf hscope
      obtain ⟨rfl,rfl⟩ := (PA194PAeq.source_relations arity r).mp hr
      obtain ⟨x,y,hx,hy,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hs,ht⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      have h := negative_atomic_replace ha hb hs ht hab
      have hva : IsSemitermVec PA194PAeq.language 1 0 (a∷(0:M)) := by simp [ha]
      have hvb : IsSemitermVec PA194PAeq.language 1 0 (b∷(0:M)) := by simp [hb]
      have h0 : IsUTermVec PA194PAeq.language 2
          (termSubst PA194PAeq.language (a∷(0:M)) x ∷ termSubst PA194PAeq.language (a∷(0:M)) y ∷ (0:M)) := by
        simp [(hva.termSubst hs).isUTerm,(hva.termSubst ht).isUTerm]
      have h1 : IsUTermVec PA194PAeq.language 2
          (termSubst PA194PAeq.language (b∷(0:M)) x ∷ termSubst PA194PAeq.language (b∷(0:M)) y ∷ (0:M)) := by
        simp [(hvb.termSubst hs).isUTerm,(hvb.termSubst ht).isUTerm]
      simp only [PA194PAeqTermBlueprint.equalityCode] at h
      rw [neg_rel (by simp [PA194PAeq.source_relations]) h0,
        neg_rel (by simp [PA194PAeq.source_relations]) h1] at h
      simpa [substs1,PA194PAeq.source_relations,hx,hy] using h
    · intro _ _
      simpa [substs1] using self_imp (^⊤ : M) (by simp)
    · intro _ _
      simpa [substs1] using self_imp (^⊥ : M) (by simp)
    · intro x y hxu hyu ihx ihy hqf hscope
      have hl : SourceDirectEdge (x ^⋏ y) x 0 := by left; exact ⟨x,y,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (x ^⋏ y) y 0 := by left; exact ⟨x,y,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsx,hsy⟩ := IsSemiformula.and.mp hscope
      have hx := ihx (internalQuantifierFree_child _ _ _ hl hqf) hsx
      have hy := ihy (internalQuantifierFree_child _ _ _ hr hqf) hsy
      have hxa := IsSemiformula.substs1 ha hsx
      have hxb := IsSemiformula.substs1 hb hsx
      have hya := IsSemiformula.substs1 ha hsy
      have hyb := IsSemiformula.substs1 hb hsy
      have h := and_imp hxa hya hxb hyb hx hy
      simpa [substs1,substs_and hxu hyu] using h
    · intro x y hxu hyu ihx ihy hqf hscope
      have hl : SourceDirectEdge (x ^⋎ y) x 0 := by right; left; exact ⟨x,y,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (x ^⋎ y) y 0 := by right; left; exact ⟨x,y,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsx,hsy⟩ := IsSemiformula.or.mp hscope
      have hx := ihx (internalQuantifierFree_child _ _ _ hl hqf) hsx
      have hy := ihy (internalQuantifierFree_child _ _ _ hr hqf) hsy
      have hxa := IsSemiformula.substs1 ha hsx
      have hxb := IsSemiformula.substs1 hb hsx
      have hya := IsSemiformula.substs1 ha hsy
      have hyb := IsSemiformula.substs1 hb hsy
      have h := or_imp hxa hya hxb hyb hx hy
      simpa [substs1,substs_or hxu hyu] using h
    · intro x hx ih hqf hscope
      exact False.elim (internalQuantifierFree_not_all x hqf)
    · intro x hx ih hqf hscope
      exact False.elim (internalQuantifierFree_not_ex x hqf)
  exact hall p hp.isUFormula hqf hp
#print axioms replace
end models
end PA194PAeqQFCongruence
