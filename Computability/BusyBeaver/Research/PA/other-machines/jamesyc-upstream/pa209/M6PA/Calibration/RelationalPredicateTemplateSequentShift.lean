module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceShift
public import M6PA.Calibration.RelationalPredicateTemplateTargetShift
public import M6PA.Calibration.RelationalPredicateTemplateSequent
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem sequentValue_sourceEigenShift (Γ : LK.Sequent sourceLanguage) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hΓ : SequentCovered Γ f) :
    sequentValue Γ⁺ (shift L P) (qqFvar 0∷targetShiftTerms f)=setShift L (sequentValue Γ P f) := by
  have hz : targetShiftTerms (0:V)=0 := by simp [targetShiftTerms]
  have hs : IsSemitermVec L (len (targetShiftTerms f)) 0 (targetShiftTerms f) := by
    simpa [NumericPAeqTerm.targetShiftTerms_length hf] using NumericPAeqTerm.targetShiftTerms_valid hf
  have he (p : Formula 0) (hp : p∈Γ) :
      formulaValue (Rewriting.shift p) (shift L P) 0 (qqFvar 0∷targetShiftTerms f)=
        shift L (formulaValue p P 0 f) := by
    rw [formulaValue_sourceShift p (show EnvironmentsValid (0:V) 0 0 (targetShiftTerms f) from ⟨by simp,hs⟩) (by simp)]
    simpa only [hz] using (formulaValue_targetShift p (n:=0) (b:=0) (f:=f) hP ⟨by simp,hf⟩ (hΓ p hp)).symm
  apply mem_ext
  intro x
  constructor
  · intro hx
    rcases (mem_sequentValue _ _ _ _).mp hx with ⟨p,hp,rfl⟩
    have hp' : ∃q∈Γ,Rewriting.shift q=p := by simpa [Rewriting.shifts] using hp
    rcases hp' with ⟨q,hq,rfl⟩
    rw [he q hq]
    exact shift_mem_setShift ((mem_sequentValue _ _ _ _).mpr ⟨q,hq,rfl⟩)
  · intro hx
    rcases mem_setShift_iff.mp hx with ⟨a,ha,rfl⟩
    rcases (mem_sequentValue _ _ _ _).mp ha with ⟨q,hq,rfl⟩
    apply (mem_sequentValue _ _ _ _).mpr
    refine ⟨Rewriting.shift q,?_,(he q hq).symm⟩
    simpa [Rewriting.shifts] using Multiset.mem_map.mpr ⟨q,hq,rfl⟩
#print axioms sequentValue_sourceEigenShift
end M6.PA.RelationalPredicateTemplate
