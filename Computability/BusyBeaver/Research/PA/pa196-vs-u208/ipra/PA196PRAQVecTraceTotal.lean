import PA196PRAQVecTraceStep

/-! In every candidate-PRA model, the parameterized tower history has the
intended bounded trace at every model-internal index. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA196PRAQVecTraceTotal
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
  PA196PRAQVecHistory PA196PRAQVecTraceMatrix PA196PRAQVecTraceStep

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩

theorem traceHistory (cons : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n seed : M) :
    traceMatrix.Eval ![n,history cons n seed,seed] Empty.elim := by
  obtain ⟨pred,_,_,hpred⟩ := PRA_proves_boundedBooleanCharacteristic
    traceMatrix traceMatrix_bounded
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hpred
  have hc := (oneCorrectSentence_iff pred traceMatrix).mp hm
  let e : ℕ → M := fun _ => seed
  have he : (fun i : Fin 1 => e i.val) = ![seed] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hbase : Structure.func (L := language) pred
      (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases (Structure.func (L := language) (firstHistory cons) (fun i : Fin 1 => e i.val))
          (fun i : Fin 1 => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
    rw [he]
    change Structure.func (L := language) pred
      ![(0 : M),Structure.func (L := language) (firstHistory cons) ![seed],seed] = _
    exact (hc _).mpr (traceBase cons hcons seed)
  have hstep : ∀ x y : M, Structure.func (L := language) pred
      (Fin.cases x (Fin.cases y (fun i : Fin 1 => e i.val))) =
        Structure.func (L := language) oneCode Fin.elim0 →
      Structure.func (L := language) pred
        (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
          (Fin.cases (Structure.func (L := language) (historyStep cons)
            (Fin.cases x (Fin.cases y (fun i : Fin 1 => e i.val))))
            (fun i : Fin 1 => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
    intro x y hy
    rw [he] at hy ⊢
    change Structure.func (L := language) pred ![x,y,seed] = _ at hy
    change Structure.func (L := language) pred
      ![Structure.func (L := language) Code.succ (fun _ => x),
        Structure.func (L := language) (historyStep cons) ![x,y,seed],seed] = _
    apply (hc _).mpr
    exact traceStep cons hcons x y seed ((hc ![x,y,seed]).mp hy)
  have h := PRAPrimitiveRecursionInduction.modelRecursiveWitness (M := M) pred
    (firstHistory cons) (historyStep cons) e hbase hstep n
  rw [he] at h
  change Structure.func (L := language) pred ![n,history cons n seed,seed] = _ at h
  exact (hc _).mp h
end models
#print axioms traceHistory
end PA196PRAQVecTraceTotal
