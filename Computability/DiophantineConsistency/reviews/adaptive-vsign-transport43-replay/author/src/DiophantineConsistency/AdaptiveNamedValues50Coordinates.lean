import DiophantineConsistency.AdaptiveNamedValues50
import DiophantineConsistency.AdaptiveCombined49Model
import DiophantineConsistency.AdaptiveNamedValues47Model
import DiophantineConsistency.AdaptiveZ43Model
import DiophantineConsistency.AdaptiveZ46Model
import DiophantineConsistency.AdaptiveZ44Model
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues50
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.beta CurrentMasks2011.radix CurrentKernel2011.K
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues22 AdaptiveNamedValues26 AdaptiveNamedValues33 AdaptiveNamedValues42
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_positive_extension_with_embedding (p : Fin 4 → ℤ) (v : Fin 42 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveNamedValues42.literal p) v)
    (rank : V) (hrank : 0<rank) (hRankRep : SignedRep (expression1 p) v (natural rank)) :
    ∃ u : Fin 50 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u ∧ (∀ i, u (embed i) = v i) := by
  let a0 : V := v 32*v 25
  let a2 : V := v 7*(v 9+v 10)
  let a4 : V := v 6+v 18*v 17
  let a5 : V := v 15*v 12
  let a6 : V := v 5*v 17
  let sp : V := (pairEval (expression3 p) v).1+1
  let sn : V := (pairEval (expression3 p) v).2+1
  let extra : Fin 8 → V := ![a0,a2,a4,a5,a6,rank,sp,sn]
  let u : Fin 50 → V := extend50 v extra
  have he : (fun i : Fin 42 => u (embed i)) = v := by
    funext i
    exact extend50_embed _ _ i
  have ha0 : 0<a0 := by dsimp [a0]; exact mul_pos (hv 32) (hv 25)
  have ha2 : 0<a2 := by dsimp [a2]; exact mul_pos (hv 7) (add_pos (hv 9) (hv 10))
  have ha4 : 0<a4 := by dsimp [a4]; exact add_pos (hv 6) (mul_pos (hv 18) (hv 17))
  have ha5 : 0<a5 := by dsimp [a5]; exact mul_pos (hv 15) (hv 12)
  have ha6 : 0<a6 := by dsimp [a6]; exact mul_pos (hv 5) (hv 17)
  have hsp : 0<sp := by dsimp [sp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hsn : 0<sn := by dsimp [sn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hextra : ∀ i : Fin 8, 0<extra i := by
    intro i
    fin_cases i <;> first | exact ha0 | exact ha2 | exact ha4 | exact ha5 | exact ha6 | exact hrank | exact hsp | exact hsn
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<42
    · simpa [u,extend50,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend50,hi] using hextra ⟨i.val-42,by omega⟩
  have hrep : ∀ i : Fin 7, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles p i)) u) := by
    intro i
    fin_cases i
    · have hr := (named_natural_reps p v).1
      have hvar : Equivalent (pairEval (holes 0) u) (natural a0) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 0)) u) (natural a0) := by
        change Equivalent (splitEval (lift (expression0 p)) u) (natural a0)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hvar : Equivalent (pairEval (holes 1) u) (natural rank) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 1)) u) (natural rank) := by
        change Equivalent (splitEval (lift (expression1 p)) u) (natural rank)
        rw [lift,splitEval_subst_var,he]
        exact hRankRep
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.1
      have hvar : Equivalent (pairEval (holes 2) u) (natural a2) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 2)) u) (natural a2) := by
        change Equivalent (splitEval (lift (expression2 p)) u) (natural a2)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hval : pairEval (lift (origHoles p 3)) u = pairEval (expression3 p) v := by
        change splitEval (lift (expression3 p)) u = splitEval (expression3 p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 3) u) (pairEval (lift (origHoles p 3)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 48) (.var 49)) u) (pairEval (expression3 p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend50, extra]
      dsimp [sp,sn,pairEval]
      ring
    · have hr := (named_natural_reps p v).2.2.1
      have hvar : Equivalent (pairEval (holes 4) u) (natural a4) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 4)) u) (natural a4) := by
        change Equivalent (splitEval (lift (expression4 p)) u) (natural a4)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.1
      have hvar : Equivalent (pairEval (holes 5) u) (natural a5) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 5)) u) (natural a5) := by
        change Equivalent (splitEval (lift (expression5 p)) u) (natural a5)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.2
      have hvar : Equivalent (pairEval (holes 6) u) (natural a6) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 6)) u) (natural a6) := by
        change Equivalent (splitEval (lift (expression6 p)) u) (natural a6)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
  have hconstraint : ∀ i : Fin 7, InternalZero (holes i-lift (origHoles p i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt p).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ?_, ?_⟩
  · exact ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3,hconstraint 4,hconstraint 5,hconstraint 6⟩
  · intro i; exact congrFun he i

end DiophantineConsistency.AdaptiveNamedValues50
