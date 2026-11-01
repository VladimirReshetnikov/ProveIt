import DiophantineConsistency.AdaptiveNamedValues33
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues33.AdaptiveVSignNamed33
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues22 AdaptiveNamedValues26 AdaptiveNamedValues33
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_oriented_extension (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveNamedValues26.literal p) v)
    (hsign : (pairEval (vExpression p) v).2 < (pairEval (vExpression p) v).1) :
    ∃ u : Fin 33 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u ∧ u 31 < u 30 := by
  let zp : V := (pairEval (zExpression p) v).1+1
  let zn : V := (pairEval (zExpression p) v).2+1
  let dp : V := (pairEval (dExpression p) v).1+1
  let dn : V := (pairEval (dExpression p) v).2+1
  let vp : V := (pairEval (vExpression p) v).1+1
  let vn : V := (pairEval (vExpression p) v).2+1
  let delta : V := (3+4*v 18)+(v 18*v 18)
  let u : Fin 33 → V := extend33 v zp zn dp dn vp vn delta
  have he : (fun i : Fin 26 => u (embed i)) = v := by
    funext i
    exact extend33_embed _ _ _ _ _ _ _ _ i
  have hzp : 0<zp := by dsimp [zp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hzn : 0<zn := by dsimp [zn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hdp : 0<dp := by dsimp [dp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hdn : 0<dn := by dsimp [dn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hvp : 0<vp := by dsimp [vp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hvn : 0<vn := by dsimp [vn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hdelta : 0<delta := by
    dsimp [delta]
    have h3 : (0:V)<3 := by simp
    exact add_pos (add_pos h3 (mul_pos (by simp) (hv 18))) (mul_pos (hv 18) (hv 18))
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<26
    · simpa [u,extend33,hi] using hv ⟨i.val,hi⟩
    · simp only [u,extend33,hi,↓reduceDIte]
      split <;> first | exact hzp | split <;> first | exact hzn | split <;> first | exact hdp | split <;> first | exact hdn | split <;> first | exact hvp | split <;> first | exact hvn | exact hdelta
  obtain ⟨hu26,hu27,hu28,hu29,hu30,hu31,hu32⟩ := extend33_last v zp zn dp dn vp vn delta
  have hrep : ∀ i : Fin 4, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles p i)) u) := by
    intro i
    fin_cases i
    · have hval : pairEval (lift (origHoles p 0)) u = pairEval (zExpression p) v := by
        change splitEval (lift (zExpression p)) u = splitEval (zExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 0) u) (pairEval (lift (origHoles p 0)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 26) (.var 27)) u) (pairEval (zExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend33]
      dsimp [zp,zn,pairEval]
      ring
    · have hval : pairEval (lift (origHoles p 1)) u = pairEval (dExpression p) v := by
        change splitEval (lift (dExpression p)) u = splitEval (dExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 1) u) (pairEval (lift (origHoles p 1)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 28) (.var 29)) u) (pairEval (dExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend33]
      dsimp [dp,dn,pairEval]
      ring
    · have hval : pairEval (lift (origHoles p 2)) u = pairEval (vExpression p) v := by
        change splitEval (lift (vExpression p)) u = splitEval (vExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 2) u) (pairEval (lift (origHoles p 2)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 30) (.var 31)) u) (pairEval (vExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend33]
      dsimp [vp,vn,pairEval]
      ring
    · have hr := delta_natural_rep p v
      have hvar : Equivalent (pairEval (holes 3) u) (natural delta) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu32]
      have hval : Equivalent (pairEval (lift (origHoles p 3)) u) (natural delta) := by
        change Equivalent (splitEval (lift (deltaExpression p)) u) (natural delta)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
  have hconstraint : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles p i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt p).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3⟩, ?_⟩
  change vn < vp
  dsimp [vn,vp]
  simpa only [add_comm] using add_lt_add_right hsign (1:V)

#print axioms exists_oriented_extension
end DiophantineConsistency.AdaptiveNamedValues33.AdaptiveVSignNamed33
