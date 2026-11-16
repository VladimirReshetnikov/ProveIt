import DiophantineConsistency.PRAHistoryFixpointSuccCode

/-! Primitive-recursive iteration of the actual PA194 occurrence-core update.
The final recursive occurrence predicate and its recursion-coverage theorem
remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
namespace PA194OccurrenceStage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryFixpointSuccCode

/-- The primitive recursion step receives `[index, previous]` while the
certified fixpoint successor code receives `[previous, index]`. -/
def stageStep (succ : Code 2) : Code 2 :=
  .comp succ (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))

def stageCode (succ : Code 2) : Code 1 := .prec (.zero 0) (stageStep succ)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

def stage (succ : Code 2) (s : M) : M := Structure.func (L := language) (stageCode succ) (fun _ => s)

theorem modelStageBase (succ : Code 2) : stage (M := M) succ 0 = 0 := by
  unfold stage stageCode
  have h := modelBase (M := M) (.zero 0) (stageStep succ) (Fin.elim0 : Fin 0 → M)
  have he : (fun i : Fin 1 => Fin.cases
      (Structure.func (L := language) (Code.zero 0) Fin.elim0) (Fin.elim0 : Fin 0 → M) i) =
      (fun _ : Fin 1 => (0 : M)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [he] at h
  exact h

theorem modelStageStep (succ : Code 2) (s : M) :
    stage succ (s+1) = Structure.func (L := language) succ ![stage succ s,s] := by
  unfold stage stageCode
  change Structure.func (L := language) (.prec (.zero 0) (stageStep succ))
    (fun _ => Structure.func (L := language) addCode ![s,Structure.func (L := language) oneCode Fin.elim0]) = _
  rw [modelAddOne]
  have h := modelStep (M := M) (.zero 0) (stageStep succ) (fun _ : Fin 1 => s)
  have hy : (fun _ : Fin 0 => s) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => s))
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) Code.succ (fun _ => s)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  change Structure.func (L := language) (.prec (.zero 0) (stageStep succ))
    (fun _ => Structure.func (L := language) Code.succ (fun _ => s)) =
    Structure.func (L := language) (stageStep succ)
      ![s,Structure.func (L := language) (.prec (.zero 0) (stageStep succ)) (fun _ => s)] at h
  rw [h]
  exact modelSwapComposition succ s _

/-- Every stage successor satisfies the exact occurrence-core update graph if
the supplied successor code has its candidate-PRA graph proof. -/
theorem modelStageStepGraph (φ : Fixpoint.Blueprint 0) (succ : Code 2)
    (hsucc : PRA ⊢ graphSentence φ succ) (s : M) :
    (Semiformula.lMap embedding φ.succDef.val).Eval
      ![stage succ (s+1),stage succ s,s] Empty.elim := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hsucc
  simp only [models_iff, graphSentence, Semiformula.eval_allClosure] at hm
  have hm := hm ![stage succ s,s]
  simp only [Semiformula.eval_rew] at hm
  have hv : (Semiterm.val (L := language) ![stage succ s,s] Empty.elim ∘
      graphRew succ ∘ Semiterm.bvar) =
      ![Structure.func (L := language) succ ![stage succ s,s],stage succ s,s] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) succ
        (Semiterm.val (L := language) ![stage succ s,s] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![stage succ s,s] Empty.elim ∘
      graphRew succ ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he] at hm
  rw [modelStageStep]
  exact hm
/-- The concrete certified collector supplies the exact membership equation at
all model stages, not only at standard natural-number stages. -/
theorem modelStageMembership (good ins bit : Code 2)
    (hbit : PRA ⊢ PRACharacteristicBit.bitSentence good)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hcorrect : PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (k s : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    bitDef.val.Evalb ![k,stage (PRAHistoryFixpointCollector.fixSuccCode good ins) (s+1)] ↔
      k ≤ s ∧ Structure.func (L := language) good
        ![k,stage (PRAHistoryFixpointCollector.fixSuccCode good ins) s] =
          Structure.func (L := language) oneCode Fin.elim0 := by
  rw [modelStageStep]
  exact modelFixSuccMembership good ins bit hbit hins hcorrect k _ s
end models

#print axioms modelStageBase
#print axioms modelStageStep
#print axioms modelStageStepGraph
#print axioms modelStageMembership
end PA194OccurrenceStage
