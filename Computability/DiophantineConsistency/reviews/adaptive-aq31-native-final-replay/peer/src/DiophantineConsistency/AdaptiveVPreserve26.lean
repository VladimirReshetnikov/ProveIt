import DiophantineConsistency.AdaptiveNamedValues26
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues26.VPreserveProbe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues22
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_preserving_extension (p : Fin 4 → ℕ) (v : Fin 22 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveNamedValues22.literal (fun i => (p i : ℤ))) v) :
    ∃ u : Fin 26 → V, (∀ i, 0<u i) ∧ InternalZero (literal (fun i => (p i : ℤ))) u ∧ (fun i : Fin 22 => u (embed i)) = v := by
  let q : V := 1+v 0*(p 0:V)
  let a : V := q*(q*q)
  let b : V := (v 6*v 7)*q
  let c : V := v 3*v 3
  let d : V := v 17*v 17
  let u : Fin 26 → V := extend26 v a b c d
  have he : (fun i : Fin 22 => u (embed i)) = v := by
    funext i
    exact extend26_embed _ _ _ _ _ i
  have hqpos : 0<q := by dsimp [q]; exact lt_of_lt_of_le (by simp : (0:V)<1) (by simp)
  have hapos : 0<a := by dsimp [a]; exact mul_pos hqpos (mul_pos hqpos hqpos)
  have hbpos : 0<b := by dsimp [b]; exact mul_pos (mul_pos (hv 6) (hv 7)) hqpos
  have hcpos : 0<c := by dsimp [c]; exact mul_pos (hv 3) (hv 3)
  have hdpos : 0<d := by dsimp [d]; exact mul_pos (hv 17) (hv 17)
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<22
    · simpa [u,extend26,hi] using hv ⟨i.val,hi⟩
    · simp only [u,extend26,hi,↓reduceDIte]
      split <;> first | exact hapos | split <;> first | exact hbpos | split <;> first | exact hcpos | exact hdpos
  obtain ⟨hu22,hu23,hu24,hu25⟩ := extend26_last v a b c d
  have hrep : ∀ i : Fin 4, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles (fun i => (p i : ℤ)) i)) u) := by
    intro i
    fin_cases i
    · have hr := (named_natural_reps p v).1
      have hvar : Equivalent (pairEval (holes 0) u) (natural a) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu22]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 0)) u) (natural a) := by
        change Equivalent (splitEval (lift (cubeExpression (fun i => (p i : ℤ)))) u) (natural a)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.1
      have hvar : Equivalent (pairEval (holes 1) u) (natural b) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu23]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 1)) u) (natural b) := by
        change Equivalent (splitEval (lift (productExpression (fun i => (p i : ℤ)))) u) (natural b)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.1
      have hvar : Equivalent (pairEval (holes 2) u) (natural c) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu24]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 2)) u) (natural c) := by
        change Equivalent (splitEval (lift (fSquareExpression (fun i => (p i : ℤ)))) u) (natural c)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2
      have hvar : Equivalent (pairEval (holes 3) u) (natural d) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu25]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 3)) u) (natural d) := by
        change Equivalent (splitEval (lift (cSquareExpression (fun i => (p i : ℤ)))) u) (natural d)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
  have hconstraint : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles (fun i => (p i : ℤ)) i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt (fun i => (p i : ℤ))).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ?_,he⟩
  exact ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3⟩


#print axioms exists_preserving_extension
end DiophantineConsistency.AdaptiveNamedValues26.VPreserveProbe
