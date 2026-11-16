import PA194ClosedAtomEnvironment
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ClosedFormulaProperty (p : V) : Prop :=
  ∀ P Q, nth P 0 = nth Q 0 → formulaFreeBound p = 0 → translateFormula P p = translateFormula Q p

theorem closedFormulaProperty_definable : 𝚷₁-Predicate (ClosedFormulaProperty : V → Prop) := by
  haveI : 𝚺₁-Function₁ (formulaFreeBound : V → V) := formulaFreeBound_defined.to_definable
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  unfold ClosedFormulaProperty
  definability

theorem closedFormulaEnvironment {p : V} (hp : IsUFormula PA194PAeq.language p) : ClosedFormulaProperty p := by
  apply IsUFormula.ISigma1.pi1_succ_induction closedFormulaProperty_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv P Q hb hz
    have hfree : atomFreeBound k v = 0 := by simpa [formulaFreeBound_rel hr hv] using hz
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    rw [translate_rel P _ _ _ hr hv,translate_rel Q _ _ _ hr hv]
    exact closedAtomEnvironment hv hfree hb (by simp) (by simp)
  · intro k r v hr hv P Q hb hz
    have hfree : atomFreeBound k v = 0 := by simpa [formulaFreeBound_nrel hr hv] using hz
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    rw [translate_nrel P _ _ _ hr hv,translate_nrel Q _ _ _ hr hv]
    rw [closedAtomEnvironment hv hfree hb (by simp) (by simp)]
  · intro P Q hb hz; simp [translate_verum]
  · intro P Q hb hz; simp [translate_falsum]
  · intro a b ha hb iha ihb P Q he hz
    have hmax : max (formulaFreeBound a) (formulaFreeBound b) = 0 := by simpa [formulaFreeBound_and ha hb] using hz
    have hza : formulaFreeBound a = 0 := le_antisymm (by simpa [hmax] using le_max_left (formulaFreeBound a) (formulaFreeBound b)) zero_le
    have hzb : formulaFreeBound b = 0 := le_antisymm (by simpa [hmax] using le_max_right (formulaFreeBound a) (formulaFreeBound b)) zero_le
    rw [translate_and P _ _ ha hb,translate_and Q _ _ ha hb,iha P Q he hza,ihb P Q he hzb]
  · intro a b ha hb iha ihb P Q he hz
    have hmax : max (formulaFreeBound a) (formulaFreeBound b) = 0 := by simpa [formulaFreeBound_or ha hb] using hz
    have hza : formulaFreeBound a = 0 := le_antisymm (by simpa [hmax] using le_max_left (formulaFreeBound a) (formulaFreeBound b)) zero_le
    have hzb : formulaFreeBound b = 0 := le_antisymm (by simpa [hmax] using le_max_right (formulaFreeBound a) (formulaFreeBound b)) zero_le
    rw [translate_or P _ _ ha hb,translate_or Q _ _ ha hb,iha P Q he hza,ihb P Q he hzb]
  · intro a ha ih P Q hb hz
    have hz' : formulaFreeBound a = 0 := by simpa [formulaFreeBound_all ha] using hz
    have hb' : nth (formulaChildParameters P) 0 = nth (formulaChildParameters Q) 0 := by
      simp [formulaChildParameters,hb]
    rw [translate_all P _ ha,translate_all Q _ ha,ih _ _ hb' hz']
  · intro a ha ih P Q hb hz
    have hz' : formulaFreeBound a = 0 := by simpa [formulaFreeBound_exs ha] using hz
    have hb' : nth (formulaChildParameters P) 0 = nth (formulaChildParameters Q) 0 := by
      simp [formulaChildParameters,hb]
    rw [translate_exs P _ ha,translate_exs Q _ ha,ih _ _ hb' hz']
#print axioms closedFormulaProperty_definable
#print axioms closedFormulaEnvironment
end generic
end PA194ClosedEnvironment
