import PA194OccurrenceStage
import PA194OccurrenceLocality
import PA194StrongInduction
import DiophantineConsistency.PRABoundedInduction

/-! Bounded stage stability for the PA194 occurrence iteration. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
namespace PA194OccurrenceStable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryFixpointSuccCode PRAHistoryFixpointCollector PRACharacteristicBit
  PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness PRABoundedInduction
open PA194OccurrenceStage PA194OccurrenceLocality

def stabilityFormula (succ bit : Code 2) : Semisentence language 2 :=
  ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0,#1])]
    ((Semiformula.rel Language.ORing.Rel.eq
      ![.func bit ![#0,.func (stageCode succ) ![#1]],.func oneCode Fin.elim0]) 🡘
     (Semiformula.rel Language.ORing.Rel.eq
      ![.func bit ![#0,.func (stageCode succ) ![.func Code.succ ![#0]]],.func oneCode Fin.elim0]))

theorem stabilityFormula_bounded (succ bit : Code 2) : Hierarchy 𝚺 0 (stabilityFormula succ bit) := by
  unfold stabilityFormula
  apply Hierarchy.ball
  · simp [Semiterm.Positive]
  · simp [LogicalConnective.iff]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : Structure.Zero language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]; rfl⟩
local instance : Structure.One language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]; rfl⟩
local instance : Structure.Add language M := ⟨fun _ _ => rfl⟩

theorem stabilityFormula_eval (succ bit : Code 2) (t : M) :
    (stabilityFormula succ bit).Eval ![t,0] Empty.elim ↔
    ∀ x < t, (Structure.func (L := language) bit ![x,stage succ t] = 1 ↔
      Structure.func (L := language) bit ![x,stage succ (x+1)] = 1) := by
  have hz (x : M) : (Semiterm.val (L := language) ![x,t,0] Empty.elim ∘
      (Fin.elim0 : Fin 0 → Semiterm language Empty 3)) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [stabilityFormula, Semiformula.eval_ball, LogicalConnective.iff,
    Semiformula.eval_rel, eqRel, Semiterm.val_func, hz]
  have vec (x : M) : (![x] : Fin 1 → M) = fun _ => x := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp only [vec, ← modelAddOne]
  have vec2 (x y : M) : (![x,y] : Fin 2 → M) = (x :> fun _ => y) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  constructor
  · intro h x hx
    have hx' : Structure.rel (L := language) Language.ORing.Rel.lt (x :> fun _ => t) := by
      change Structure.rel (L := language) Language.ORing.Rel.lt ![x,t] at hx
      simpa only [vec2] using hx
    have hh := h x hx'
    change (Structure.func (L := language) bit (x :> fun _ => stage succ t) = Structure.func (L := language) oneCode Fin.elim0 ↔
      Structure.func (L := language) bit (x :> fun _ => stage succ (Structure.func (L := language) addCode ![x,Structure.func (L := language) oneCode Fin.elim0])) = Structure.func (L := language) oneCode Fin.elim0)
    simpa only [stage, vec2, iff_def] using hh
  · intro h x hx
    have hx' : x < t := by
      change Structure.rel (L := language) Language.ORing.Rel.lt ![x,t]
      simpa only [vec2] using hx
    have hh := h x hx'
    change (Structure.func (L := language) bit (x :> fun _ => stage succ t) = Structure.func (L := language) oneCode Fin.elim0 ↔
      Structure.func (L := language) bit (x :> fun _ => stage succ (Structure.func (L := language) addCode ![x,Structure.func (L := language) oneCode Fin.elim0])) = Structure.func (L := language) oneCode Fin.elim0) at hh
    simpa only [stage, vec2, iff_def] using hh

/-- Strong induction over the bounded invariant, valid at nonstandard stages.
The update equation is supplied explicitly. -/
theorem modelStageStability (succ bit : Code 2)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (hrec : ∀ k s : M,
      bitDef.val.Evalb ![k,stage succ (s+1)] ↔
        k ≤ s ∧ PA194OccurrenceCore.occurrenceCore.val.Evalb ![k,stage succ s]) :
    ∀ t x : M, x < t →
      (bitDef.val.Evalb ![x,stage succ t] ↔ bitDef.val.Evalb ![x,stage succ (x+1)]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit
  have hb (x h : M) : Structure.func (L := language) bit ![x,h] = 1 ↔
      bitDef.val.Evalb ![x,h] := by
    have hh := (oneCorrectSentence_iff bit PRAHistoryInsertCode.bitGraph).mp hm ![x,h]
    rw [PRAHistoryInsertCode.bitGraph, Semiformula.eval_lMap,
      PRAModelIOpenPairing.reduct_eq_standard] at hh
    exact hh
  obtain ⟨good, _, _, hgood⟩ := PRA_proves_boundedBooleanCharacteristic
    (stabilityFormula succ bit) (stabilityFormula_bounded succ bit)
  have hgoodModel := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hgood
  have hgood' (t : M) : PA194StrongInduction.value good t 0 = 1 ↔
      ∀ x < t, (bitDef.val.Evalb ![x,stage succ t] ↔
        bitDef.val.Evalb ![x,stage succ (x+1)]) := by
    have hh := (oneCorrectSentence_iff good (stabilityFormula succ bit)).mp hgoodModel ![t,0]
    rw [stabilityFormula_eval] at hh
    exact hh.trans (forall_congr' fun x => forall_congr' fun _ => iff_congr (hb x _) (hb x _))
  have hall : ∀ t : M, PA194StrongInduction.value good t 0 = 1 := by
    apply PA194StrongInduction.modelStrongCode good 0
    intro n ih
    apply (hgood' n).mpr
    intro x hx
    rcases zero_or_succ n with rfl | ⟨t,rfl⟩
    · exact False.elim (not_lt_zero hx)
    have hxt : x ≤ t := lt_succ_iff_le.mp hx
    rcases lt_or_eq_of_le hxt with hlt | rfl
    · have ht := (hgood' t).mp (ih t (lt_succ_iff_le.mpr (le_refl t)))
      have hxgood := (hgood' x).mp (ih x hx)
      have hloc : PA194OccurrenceCore.occurrenceCore.val.Evalb ![x,stage succ t] ↔
          PA194OccurrenceCore.occurrenceCore.val.Evalb ![x,stage succ x] := by
        apply core_local
        intro y hy
        exact (ht y (lt_trans hy hlt)).trans (hxgood y hy).symm
      rw [hrec x t, hrec x x]
      simpa [le_of_lt hlt] using hloc
    · rfl
  intro t x hx
  exact (hgood' t).mp (hall t) x hx

end models
#print axioms stabilityFormula_eval
#print axioms modelStageStability
end PA194OccurrenceStable
