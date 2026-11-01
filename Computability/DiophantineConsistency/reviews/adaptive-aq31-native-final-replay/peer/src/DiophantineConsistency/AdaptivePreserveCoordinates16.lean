import DiophantineConsistency.AdaptiveMainScaleWitness16
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace DiophantineConsistency.AdaptiveSquareWitnessDirect14
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveDirectOrdinateSquareSums AdaptiveFirstRootFactor87Context
open ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_positive_extension_with_coordinates (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hv : ∀ i, 0 < v i) (hz : InternalZero (optimized p) v)
    (hm : 0 < magnitude (pairEval (vExpression p) v)) :
    ∃ u : Fin 14 → V, (∀ i, 0 < u i) ∧ InternalZero (literal p) u ∧ (fun i => u (embed i)) = v := by
  let m := magnitude (pairEval (vExpression p) v)
  let u : Fin 14 → V := extend v (m*m)
  have he : (fun i : Fin 13 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0 < u i := by
    intro i
    by_cases hi : i.val<13
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi,m] using mul_pos hm hm
  have hvexpr : pairEval (liftedV p) u = pairEval (vExpression p) v := by
    change splitEval (liftedV p) u = splitEval (vExpression p) v
    rw [liftedV,splitEval_subst_var,he]
  have hs : Equivalent (pairEval (liftedV p * liftedV p) u) (natural (m*m)) := by
    change Equivalent (multiply (pairEval (liftedV p) u) (pairEval (liftedV p) u)) (natural (m*m))
    rw [hvexpr]
    exact square_magnitude _
  have hw : Equivalent (pairEval w u) (natural (m*m)) := by
    change Equivalent (pairEval (.var 13) u) (natural (m*m))
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 13=m*m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedV p*liftedV p) u) :=
    equivalent_trans hw (equivalent_symm hs)
  have hc : InternalZero (w-liftedV p*liftedV p) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt p).subst (fill w)) u :=
    (context_zero_iff_of_constraint p u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts p u).mpr ⟨hcontext,hc⟩,he⟩
#print axioms exists_positive_extension_with_coordinates
end DiophantineConsistency.AdaptiveSquareWitnessDirect14
namespace DiophantineConsistency.AdaptiveScaleWitness15
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_positive_extension_with_coordinates (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hv : ∀ i, 0<v i)
    (hz : InternalZero (AdaptiveSquareWitnessDirect14.literal (fun j => (p j:ℤ))) v) :
    ∃ u : Fin 15 → V, (∀ i, 0<u i) ∧ InternalZero (literal (fun j => (p j:ℤ))) u ∧ (fun i => u (embed i)) = v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let m : V := q*(q*q)*b
  have hb' : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := add_pos (by simp) hb'
  have hm : 0<m := mul_pos (mul_pos hq (mul_pos hq hq)) hb'
  let u : Fin 15 → V := extend v m
  have he : (fun i : Fin 14 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<14
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi] using hm
  have hscale : SignedRep (liftedScale (fun j => (p j:ℤ))) u (natural m) := by
    change Equivalent (splitEval (liftedScale (fun j => (p j:ℤ))) u) (natural m)
    rw [liftedScale,splitEval_subst_var,he]
    exact scale_rep p v
  have hw : Equivalent (pairEval w u) (natural m) := by
    change Equivalent (pairEval (.var 14) u) (natural m)
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 14=m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedScale (fun j => (p j:ℤ))) u) :=
    equivalent_trans hw (equivalent_symm hscale)
  have hc : InternalZero (w-liftedScale (fun j => (p j:ℤ))) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt (fun j => (p j:ℤ))).subst (fill w)) u :=
    (context_zero_iff_of_constraint _ u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hc⟩,he⟩
#print axioms exists_positive_extension_with_coordinates
end DiophantineConsistency.AdaptiveScaleWitness15
namespace DiophantineConsistency.AdaptiveMainScaleWitness16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveDirectOrdinateSquareSums

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem exists_positive_extension_with_coordinates (p : Fin 4 → ℕ) (v : Fin 15 → V)
    (hb : 0<(p 0:V)) (hv : ∀ i, 0<v i)
    (hz : InternalZero (AdaptiveScaleWitness15.literal (fun j => (p j:ℤ))) v) :
    ∃ u : Fin 16 → V, (∀ i, 0<u i) ∧ InternalZero (literal (fun j => (p j:ℤ))) u ∧ (fun i => u (embed i)) = v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let m : V := v 7*(q*q)
  have hb' : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := add_pos (by simp) hb'
  have hm : 0<m := mul_pos (hv 7) (mul_pos hq hq)
  let u : Fin 16 → V := extend v m
  have he : (fun i : Fin 15 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<15
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi] using hm
  have hscale : SignedRep (liftedScale (fun j => (p j:ℤ))) u (natural m) := by
    change Equivalent (splitEval (liftedScale (fun j => (p j:ℤ))) u) (natural m)
    rw [liftedScale,splitEval_subst_var,he]
    exact scale_rep p v
  have hw : Equivalent (pairEval w u) (natural m) := by
    change Equivalent (pairEval (.var 15) u) (natural m)
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 15=m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedScale (fun j => (p j:ℤ))) u) :=
    equivalent_trans hw (equivalent_symm hscale)
  have hc : InternalZero (w-liftedScale (fun j => (p j:ℤ))) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt (fun j => (p j:ℤ))).subst (fill w)) u :=
    (context_zero_iff_of_constraint _ u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hc⟩,he⟩
#print axioms exists_positive_extension_with_coordinates
end DiophantineConsistency.AdaptiveMainScaleWitness16
