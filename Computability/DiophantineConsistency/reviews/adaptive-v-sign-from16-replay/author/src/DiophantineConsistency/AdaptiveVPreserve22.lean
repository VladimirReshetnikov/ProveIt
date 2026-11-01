import DiophantineConsistency.AdaptiveNamedValues22
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues22.VPreserveProbe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_preserving_extension (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveRankWitness17.literal p) v) :
    ∃ u : Fin 22 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u ∧ (fun i : Fin 17 => u (embed i)) = v := by
  let c : V := v 9+v 7*(v 9+v 10)
  let a : V := v 6*v 7+v 7
  let ell : V := (v 6*v 7)*(v 7*(v 9+v 10))
  let wp : V := (pairEval (wExpression p) v).1+1
  let wn : V := (pairEval (wExpression p) v).2+1
  let u : Fin 22 → V := extend22 v c a ell wp wn
  have he : (fun i : Fin 17 => u (embed i)) = v := by
    funext i
    exact extend22_embed _ _ _ _ _ _ i
  have hcpos : 0<c := by dsimp [c]; exact add_pos (hv 9) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  have hapos : 0<a := by dsimp [a]; exact add_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hellpos : 0<ell := by dsimp [ell]; exact mul_pos (mul_pos (hv 6) (hv 7)) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  have hwppos : 0<wp := by dsimp [wp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hwnpos : 0<wn := by dsimp [wn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<17
    · simpa [u,extend22,hi] using hv ⟨i.val,hi⟩
    · simp only [u,extend22,hi,↓reduceDIte]
      split <;> first | exact hcpos | split <;> first | exact hapos | split <;> first | exact hellpos | split <;> first | exact hwppos | exact hwnpos
  obtain ⟨hu17,hu18,hu19,hu20,hu21⟩ := extend22_last v c a ell wp wn
  have hrep : ∀ i : Fin 4, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles p i)) u) := by
    intro i
    fin_cases i
    · have hr := (named_natural_reps p v).1
      have hvar : Equivalent (pairEval (holes 0) u) (natural c) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu17]
      have hval : Equivalent (pairEval (lift (origHoles p 0)) u) (natural c) := by
        change Equivalent (splitEval (lift (cExpression p)) u) (natural c)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.1
      have hvar : Equivalent (pairEval (holes 1) u) (natural a) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu18]
      have hval : Equivalent (pairEval (lift (origHoles p 1)) u) (natural a) := by
        change Equivalent (splitEval (lift (aExpression p)) u) (natural a)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2
      have hvar : Equivalent (pairEval (holes 2) u) (natural ell) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu19]
      have hval : Equivalent (pairEval (lift (origHoles p 2)) u) (natural ell) := by
        change Equivalent (splitEval (lift (ellExpression p)) u) (natural ell)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hval : pairEval (lift (origHoles p 3)) u = pairEval (wExpression p) v := by
        change splitEval (lift (wExpression p)) u = splitEval (wExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 3) u) (pairEval (lift (origHoles p 3)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 20) (.var 21)) u) (pairEval (wExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend22]
      dsimp [wp,wn,pairEval]
      ring
  have hconstraint : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles p i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt p).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ?_,he⟩
  exact ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3⟩


#print axioms exists_preserving_extension
end DiophantineConsistency.AdaptiveNamedValues22.VPreserveProbe
