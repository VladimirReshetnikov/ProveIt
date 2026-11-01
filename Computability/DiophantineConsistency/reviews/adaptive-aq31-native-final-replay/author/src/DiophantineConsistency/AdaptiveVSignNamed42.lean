import DiophantineConsistency.AdaptiveNamedValues42
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues42.AdaptiveVSignNamed42
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues22 AdaptiveNamedValues26 AdaptiveNamedValues33 AdaptiveNamedValues42
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_oriented_extension (p : Fin 4 → ℕ) (v : Fin 33 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveNamedValues33.literal (fun i => (p i : ℤ))) v)
    (hsign : v 31 < v 30) :
    ∃ u : Fin 42 → V, (∀ i, 0<u i) ∧ InternalZero (literal (fun i => (p i : ℤ))) u ∧ u 31 < u 30 := by
  let q : V := 1+v 0*(p 0:V)
  let a0 : V := q*q
  let a1 : V := v 6*v 7
  let a2 : V := v 14*v 14
  let a3 : V := v 19*(v 19+(v 9+v 10))
  let a4 : V := v 15*v 15
  let a5 : V := v 25*v 4
  let a6 : V := v 11*v 11
  let wp : V := (pairEval (expression7 (fun i => (p i : ℤ))) v).1+1
  let wn : V := (pairEval (expression7 (fun i => (p i : ℤ))) v).2+1
  let extra : Fin 9 → V := ![a0,a1,a2,a3,a4,a5,a6,wp,wn]
  let u : Fin 42 → V := extend42 v extra
  have he : (fun i : Fin 33 => u (embed i)) = v := by
    funext i
    exact extend42_embed _ _ i
  have hqpos : 0<q := by dsimp [q]; exact lt_of_lt_of_le (by simp : (0:V)<1) (by simp)
  have ha0 : 0<a0 := by dsimp [a0]; exact mul_pos hqpos hqpos
  have ha1 : 0<a1 := by dsimp [a1]; exact mul_pos (hv 6) (hv 7)
  have ha2 : 0<a2 := by dsimp [a2]; exact mul_pos (hv 14) (hv 14)
  have ha3 : 0<a3 := by dsimp [a3]; exact mul_pos (hv 19) (add_pos (hv 19) (add_pos (hv 9) (hv 10)))
  have ha4 : 0<a4 := by dsimp [a4]; exact mul_pos (hv 15) (hv 15)
  have ha5 : 0<a5 := by dsimp [a5]; exact mul_pos (hv 25) (hv 4)
  have ha6 : 0<a6 := by dsimp [a6]; exact mul_pos (hv 11) (hv 11)
  have hwp : 0<wp := by dsimp [wp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hwn : 0<wn := by dsimp [wn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hextra : ∀ i : Fin 9, 0<extra i := by
    intro i
    fin_cases i <;> first | exact ha0 | exact ha1 | exact ha2 | exact ha3 | exact ha4 | exact ha5 | exact ha6 | exact hwp | exact hwn
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<33
    · simpa [u,extend42,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend42,hi] using hextra ⟨i.val-33,by omega⟩
  have hrep : ∀ i : Fin 8, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles (fun i => (p i : ℤ)) i)) u) := by
    intro i
    fin_cases i
    · have hr := (named_natural_reps p v).1
      have hvar : Equivalent (pairEval (holes 0) u) (natural a0) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 0)) u) (natural a0) := by
        change Equivalent (splitEval (lift (expression0 (fun i => (p i : ℤ)))) u) (natural a0)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.1
      have hvar : Equivalent (pairEval (holes 1) u) (natural a1) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 1)) u) (natural a1) := by
        change Equivalent (splitEval (lift (expression1 (fun i => (p i : ℤ)))) u) (natural a1)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.1
      have hvar : Equivalent (pairEval (holes 2) u) (natural a2) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 2)) u) (natural a2) := by
        change Equivalent (splitEval (lift (expression2 (fun i => (p i : ℤ)))) u) (natural a2)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.1
      have hvar : Equivalent (pairEval (holes 3) u) (natural a3) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 3)) u) (natural a3) := by
        change Equivalent (splitEval (lift (expression3 (fun i => (p i : ℤ)))) u) (natural a3)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.2.1
      have hvar : Equivalent (pairEval (holes 4) u) (natural a4) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 4)) u) (natural a4) := by
        change Equivalent (splitEval (lift (expression4 (fun i => (p i : ℤ)))) u) (natural a4)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.2.2.1
      have hvar : Equivalent (pairEval (holes 5) u) (natural a5) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 5)) u) (natural a5) := by
        change Equivalent (splitEval (lift (expression5 (fun i => (p i : ℤ)))) u) (natural a5)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.2.2.2
      have hvar : Equivalent (pairEval (holes 6) u) (natural a6) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend42, extra]
      have hval : Equivalent (pairEval (lift (origHoles (fun i => (p i : ℤ)) 6)) u) (natural a6) := by
        change Equivalent (splitEval (lift (expression6 (fun i => (p i : ℤ)))) u) (natural a6)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hval : pairEval (lift (origHoles (fun i => (p i : ℤ)) 7)) u = pairEval (expression7 (fun i => (p i : ℤ))) v := by
        change splitEval (lift (expression7 (fun i => (p i : ℤ)))) u = splitEval (expression7 (fun i => (p i : ℤ))) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 7) u) (pairEval (lift (origHoles (fun i => (p i : ℤ)) 7)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 40) (.var 41)) u) (pairEval (expression7 (fun i => (p i : ℤ))) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend42, extra]
      dsimp [wp,wn,pairEval]
      ring
  have hconstraint : ∀ i : Fin 8, InternalZero (holes i-lift (origHoles (fun i => (p i : ℤ)) i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt (fun i => (p i : ℤ))).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3,hconstraint 4,hconstraint 5,hconstraint 6,hconstraint 7⟩, ?_⟩
  have h31 := congrFun he 31
  have h30 := congrFun he 30
  change u 31 = v 31 at h31
  change u 30 = v 30 at h30
  simpa only [h31,h30] using hsign


#print axioms exists_oriented_extension
end DiophantineConsistency.AdaptiveNamedValues42.AdaptiveVSignNamed42
