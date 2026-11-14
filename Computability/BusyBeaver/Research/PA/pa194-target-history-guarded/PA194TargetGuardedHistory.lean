import PA194TargetExtendedStep
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetGuardedHistory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory

/-- Inputs are stage, reverse history, line vector and its declared length. -/
noncomputable def next : Code 4 :=
  selectAmong (bin ltBitCode (.proj 0) (.proj 3))
    (app3 extended (.proj 0) (.proj 1) (bin lookup (.proj 0) (.proj 2))) (.zero 4)
noncomputable def history : Code 3 := PA194ParamHistory.historyCode next
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem next_model (n hist program len : M) :
    F next ![n,hist,program,len] =
      if n < len then F extended ![n,hist,program.[n]] else 0 := by
  simp only [next,modelChooseLess,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  change (if n < len then F (app3 extended (.proj 0) (.proj 1) (bin lookup (.proj 0) (.proj 2))) ![n,hist,program,len] else F (.zero 4) ![n,hist,program,len]) = _
  by_cases h : n < len
  · rw [if_pos h,if_pos h,app3_model,modelProjection,modelProjection,modelBin,modelProjection,modelProjection]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change F extended ![n,hist,F lookup ![n,program]] = _
    have hv : F lookup ![n,program] = program.[n] := PA194SearchVector.lookup_nth n program
    rw [hv]
  · rw [if_neg h,if_neg h,PRAMultiplication.modelZero]
    rfl

theorem history_step (n program len : M) :
    F history ![n+1,program,len] =
      pair (if n < len then F extended ![n,F history ![n,program,len],program.[n]] else 0)
        (F history ![n,program,len])+1 := by
  rw [history,PA194ParamHistory.modelStep,next_model]

theorem history_newest (n program len : M) :
    F lookup ![0,F history ![n+1,program,len]] =
      if n < len then F extended ![n,F history ![n,program,len],program.[n]] else 0 := by
  rw [history_step]
  exact modelLookupZero firstProjection secondProjection firstProjection_certified _ _

theorem history_earlier (n i program len : M) :
    F lookup ![i+1,F history ![n+1,program,len]] =
      F lookup ![i,F history ![n,program,len]] := by
  rw [history_step]
  exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified _ _ _

theorem past_end_rejects (n hist program len : M) (h : len ≤ n) :
    F next ![n,hist,program,len] = 0 := by
  rw [next_model,if_neg (not_lt_of_ge h)]

theorem history_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (program len n : M) : GoodHistory G n (F history ![n,program,len]) := by
  have hf : 𝚺₁-Function₁ (fun n : M => F history ![n,program,len]) :=
    PA194CodeInstance.unary_of_three history program len
  have hdef := relation_substitution_def (GoodHistory G) _ (goodHistory_definable G hG) hf
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero =>
    intro i hi
    exact False.elim (not_lt_zero hi)
  | succ n ih =>
    intro i hi
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · rw [history_newest]
      by_cases hn : n < len
      · rw [if_pos hn]
        exact extended_sound G hLeaf hGen hMP hNew n _ _ ih
      · rw [if_neg hn]
        exact Or.inl rfl
    · rw [history_earlier]
      apply ih j
      exact (add_lt_add_iff_right 1).mp hi

theorem accepted_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (program len n i v : M) (hi : i < n)
    (hv : F lookup ![i,F history ![n,program,len]] = v+1) : G v := by
  have h := history_sound G hG hLeaf hGen hMP hNew program len n i hi
  rw [hv] at h
  exact (good_value_accepted G v).mp h

#print axioms next_model
#print axioms past_end_rejects
#print axioms history_sound
#print axioms accepted_sound
end models
end PA194TargetGuardedHistory
