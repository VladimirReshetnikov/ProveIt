import PA194PAeqInductionClosureReduction
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem closeOne_close (n p : V) : close n (closeOne p) = closeOne (close n p) := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  haveI : 𝚺₁-Function₂ (bindFormula : V → V → V) := bindFormula_defined.to_definable
  haveI : 𝚺₁-Function₁ (closeOne : V → V) := by unfold closeOne; definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ n ih => simp only [close_succ,ih]

def OneStepReconstruction : Prop := ∀ m b : V,
  IsSemiformula language (m+1) b → shift language b = b →
  closeOne (subst language (fvarVec (m+1)) b) =
    subst language (fvarVec m) (^∀ b)

theorem closureReconstruction_of_oneStep (hstep : OneStepReconstruction (V := V)) :
    ClosureReconstruction (V := V) := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  have hdef : 𝚷₁-Predicate (fun m : V => ∀ b : V, IsSemiformula language m b →
      shift language b = b → close m (subst language (fvarVec m) b) = qqAlls b m) := by
    definability
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => exact hdef
  | zero =>
    intro b hb hs
    simp only [fvarVec_zero,close_zero,qqAlls_zero]
    apply subst_eq_self hb (by simp) (by simp)
  | succ m ih =>
    intro b hb hs
    have hb' : IsSemiformula language m (^∀ b) := by
      exact IsSemiformula.all.mpr hb
    have hs' : shift language (^∀ b) = ^∀ b := by simp [shift_all hb.isUFormula,hs]
    rw [close_succ,← closeOne_close, hstep m b hb hs, ih (^∀ b) hb' hs', qqAlls_succ']
/-- The pointwise reconstruction left after reducing model-valued closure iteration. -/
def BindSubstReconstruction : Prop := ∀ m b : V,
  IsSemiformula language (m+1) b → shift language b = b →
  bindFormula 0 (subst language (fvarVec (m+1)) b) =
    subst language (qVec language (fvarVec m)) b

theorem oneStep_of_bindSubst (h : BindSubstReconstruction (V := V)) :
    OneStepReconstruction (V := V) := by
  intro m b hb hs
  rw [closeOne,substs_all hb.isUFormula,h m b hb hs]

theorem induction_supplier_of_bindSubst (h : BindSubstReconstruction (V := V)) :
    ∀ p : V, InductionUnivR p → Provable ordinaryPAeq (PA194PAeqTermBlueprint.formulaCode 0 p) :=
  induction_supplier_of_closure_reconstruction (closureReconstruction_of_oneStep (oneStep_of_bindSubst h))
#print axioms induction_supplier_of_bindSubst
#print axioms closeOne_close
#print axioms closureReconstruction_of_oneStep
end PA194PAeq.InductionReopen
