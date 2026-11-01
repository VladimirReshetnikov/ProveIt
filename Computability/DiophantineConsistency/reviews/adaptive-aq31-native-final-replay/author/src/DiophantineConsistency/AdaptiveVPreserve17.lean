import DiophantineConsistency.AdaptiveRankWitness17
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveRankWitness17.VPreserveProbe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveDirectOrdinateSquareSums
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_preserving_extension (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveMainScaleWitness16.literal p) v)
    (m : V) (hm : 0<m) (hr : SignedRep (rankExpression p) v (natural m)) :
    ∃ u : Fin 17 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u ∧ (fun i : Fin 16 => u (embed i)) = v := by
  let u : Fin 17 → V := extend v m
  have he : (fun i : Fin 16 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<16
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi] using hm
  have hrank : SignedRep (liftedRank p) u (natural m) := by
    change Equivalent (splitEval (liftedRank p) u) (natural m)
    rw [liftedRank,splitEval_subst_var,he]
    exact hr
  have hw : Equivalent (pairEval w u) (natural m) := by
    change Equivalent (pairEval (.var 16) u) (natural m)
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 16=m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedRank p) u) :=
    equivalent_trans hw (equivalent_symm hrank)
  have hc : InternalZero (w-liftedRank p) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt p).subst (fill w)) u :=
    (context_zero_iff_of_constraint _ u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hc⟩,he⟩

#print axioms exists_preserving_extension
end DiophantineConsistency.AdaptiveRankWitness17.VPreserveProbe
