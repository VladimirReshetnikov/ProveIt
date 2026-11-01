import DiophantineConsistency.AdaptiveDirectOrdinate86Lift
import DiophantineConsistency.ArithmeticAdaptiveOrdinateGap2011

/-! Conditional signed-square facts for direct ordinate witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Lift
open ArithmeticSignedPairs ArithmeticAdaptiveOrdinateGap2011 ArithmeticPellHalfIndex

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A signed square equals the natural square of its magnitude. -/
theorem square_magnitude (p : Pair V) :
    Equivalent (multiply p p) (natural (magnitude p*magnitude p)) := by
  wlog h : p.2 ≤ p.1 generalizing p
  · have hh := this (swap p) (le_of_not_ge h)
    rw [multiply_swap_left, multiply_swap_right, magnitude_swap] at hh
    simpa only [swap, Prod.eta] using hh
  let u := p.1-p.2
  have hu : p.1=p.2+u := by rw [add_comm,tsub_add_cancel_of_le h]
  rw [magnitude_of_add hu]
  change p.1*p.1+p.2*p.2+0=(p.1*p.2+p.2*p.1)+u*u
  rw [hu]; ring

/-- A direct ordinate matching the old signed magnitude makes the two
    literal squared-ordinate substitutions equivalent. -/
theorem squared_ordinate_equiv (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (h : magnitude ((splitEval (signedV p) v).1+v 13,
      (splitEval (signedV p) v).2)=v 11) :
    Equivalent (splitEval (oldSquare p) v) (splitEval newSquare v) := by
  simp only [oldSquare,newSquare,splitEval_mul,splitEval_add]
  have h13 : splitEval (.var 13 : Expr (Fin 14)) v = natural (v 13) := by
    simp [splitEval,Expr.splitNatural,NatExpr.evalSemiring,natural]
  have h11 : splitEval (.var 11 : Expr (Fin 14)) v = natural (v 11) := by
    simp [splitEval,Expr.splitNatural,NatExpr.evalSemiring,natural]
  rw [h13,h11]
  have ht := square_magnitude ((splitEval (signedV p) v).1+v 13,
    (splitEval (signedV p) v).2)
  rw [h] at ht
  simpa only [pairAdd,pairMul,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using ht

/-- The signed expression does not use the separate old-offset slot. -/
theorem signedV_update_offset (p : Fin 4 → ℤ) (v : Fin 14 → V) (u : V) :
    splitEval (signedV p) (Function.update v 13 u) = splitEval (signedV p) v := by
  simp only [signedV,splitEval_add,splitEval_sub,splitEval_mul]
  simp [splitEval,Expr.splitNatural,NatExpr.evalSemiring,Function.update]

private theorem embed_ne_offset (i : Fin 13) : embed i ≠ 13 := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [embed,Fin.val_mk] at hv
  omega

/-- A candidate zero with a strict signed-ordinate gap gives an old-expression
    zero with a positive recovered offset. The gap is an explicit premise. -/
theorem new_zero_to_old_of_gap (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hgap : magnitude (splitEval (signedV p) v)<v 11)
    (hz : AdaptiveEquationSyntax2011.InternalZero (expressionAt86 p)
      (fun i => v (embed i))) :
    ∃ u : V, 0<u ∧ AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveFirstRootFactor87Literal.expressionAt87 p)
      (fun i => if i=11 then u else v (embed i)) := by
  obtain ⟨u,hu,_,humag⟩ := positive_offset_of_gap hgap
  let w := Function.update v 13 u
  have he : splitEval (signedV p) w=splitEval (signedV p) v := by
    exact signedV_update_offset p v u
  have hmag : magnitude ((splitEval (signedV p) w).1+w 13,
      (splitEval (signedV p) w).2)=w 11 := by
    rw [he]
    have hw13 : w 13=u := by simp [w]
    have hw11 : w 11=v 11 := by simp [w]
    rw [hw13,hw11]
    exact humag
  have hiff := conditional_unshifted_zero_iff p w (squared_ordinate_equiv p w hmag)
  have hnew : (fun i => w (embed i)) = (fun i => v (embed i)) := by
    funext i
    simp [w,embed_ne_offset i]
  have hold : (fun i => w (oldIndex i)) =
      (fun i => if i=11 then u else v (embed i)) := by
    funext i
    by_cases hi : i=11
    · simp [oldIndex,hi,w]
    · simp [oldIndex,hi,w,embed_ne_offset i]
  rw [hnew,hold] at hiff
  exact ⟨u,hu,hiff.mpr hz⟩

/-- The signed expression does not use the direct-ordinate slot either. -/
theorem signedV_update_ordinate (p : Fin 4 → ℤ) (v : Fin 14 → V) (y : V) :
    splitEval (signedV p) (Function.update v 11 y) = splitEval (signedV p) v := by
  simp only [signedV,splitEval_add,splitEval_sub,splitEval_mul]
  simp [splitEval,Expr.splitNatural,NatExpr.evalSemiring,Function.update]

private theorem oldIndex_ne_ordinate (i : Fin 13) : oldIndex i ≠ 11 := by
  by_cases h : i=11
  · simp [oldIndex,h]
  · intro he
    have hv := congrArg Fin.val he
    have hi : i.val ≠ 11 := by
      intro hval
      apply h
      exact Fin.ext hval
    simp only [oldIndex,h,if_false,embed,Fin.val_mk] at hv
    exact hi hv

/-- An old-expression zero whose signed ordinate magnitude is positive gives
    a candidate zero with that magnitude as the direct ordinate. -/
theorem old_zero_to_new_of_positive_magnitude (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hpos : 0<magnitude ((splitEval (signedV p) v).1+v 13,
      (splitEval (signedV p) v).2))
    (hz : AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveFirstRootFactor87Literal.expressionAt87 p) (fun i => v (oldIndex i))) :
    ∃ y : V, 0<y ∧ AdaptiveEquationSyntax2011.InternalZero (expressionAt86 p)
      (fun i => if i=11 then y else v (embed i)) := by
  let y : V := magnitude ((splitEval (signedV p) v).1+v 13,
    (splitEval (signedV p) v).2)
  let w := Function.update v 11 y
  have he : splitEval (signedV p) w=splitEval (signedV p) v := by
    exact signedV_update_ordinate p v y
  have hmag : magnitude ((splitEval (signedV p) w).1+w 13,
      (splitEval (signedV p) w).2)=w 11 := by
    rw [he]
    have hw13 : w 13=v 13 := by simp [w]
    have hw11 : w 11=y := by simp [w]
    rw [hw13,hw11]
  have hiff := conditional_unshifted_zero_iff p w (squared_ordinate_equiv p w hmag)
  have hold : (fun i => w (oldIndex i)) = (fun i => v (oldIndex i)) := by
    funext i
    simp [w,oldIndex_ne_ordinate i]
  have hnew : (fun i => w (embed i)) =
      (fun i => if i=11 then y else v (embed i)) := by
    funext i
    by_cases hi : i=11
    · simp [hi,w,embed]
    · have hembed : embed i ≠ 11 := by
        intro he'
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val he'
        simp only [embed,Fin.val_mk] at hv
        omega
      simp [hi,w,hembed]
  rw [hold,hnew] at hiff
  exact ⟨y,hpos,hiff.mp hz⟩

/-- An unshifted positive zero gives a zero of the natural shifted expression. -/
theorem shifted_zero_of_positive {e : Expr (Fin 13)} {v : Fin 13 → V}
    (hv : ∀ i, 0<v i) (hz : AdaptiveEquationSyntax2011.InternalZero e v) :
    AdaptiveEquationSyntax2011.InternalZero (AdaptiveEquationSyntax2011.positiveShift e)
      (fun i => v i-1) := by
  rw [AdaptiveEquationSyntax2011.internalZero_positiveShift]
  have he : (fun i => (v i-1)+1)=v := by
    funext i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hv i))
  rw [he]
  exact hz

/-- Under the strict signed-ordinate gap, a positive candidate zero gives a
    natural zero of the old shifted literal. -/
theorem new_positive_zero_to_old_natural_of_gap (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hv : ∀ i : Fin 13, 0<v (embed i))
    (hgap : magnitude (splitEval (signedV p) v)<v 11)
    (hz : AdaptiveEquationSyntax2011.InternalZero (expressionAt86 p)
      (fun i => v (embed i))) :
    ∃ w : Fin 13 → V, AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveEquationSyntax2011.positiveShift
        (AdaptiveFirstRootFactor87Literal.expressionAt87 p)) w := by
  obtain ⟨u,hu,hold⟩ := new_zero_to_old_of_gap p v hgap hz
  let w : Fin 13 → V := fun i => if i=11 then u else v (embed i)
  have hw : ∀ i, 0<w i := by
    intro i
    by_cases hi : i=11
    · simpa [w,hi] using hu
    · simpa [w,hi] using hv i
  exact ⟨fun i => w i-1,shifted_zero_of_positive hw hold⟩

/-- With positive old coordinates and positive ordinate magnitude, an old
    zero gives a natural zero of the direct-ordinate shifted literal. -/
theorem old_positive_zero_to_new_natural_of_magnitude (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hv : ∀ i : Fin 13, 0<v (oldIndex i))
    (hpos : 0<magnitude ((splitEval (signedV p) v).1+v 13,
      (splitEval (signedV p) v).2))
    (hz : AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveFirstRootFactor87Literal.expressionAt87 p) (fun i => v (oldIndex i))) :
    ∃ w : Fin 13 → V, AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveEquationSyntax2011.positiveShift (expressionAt86 p)) w := by
  obtain ⟨y,hy,hnew⟩ := old_zero_to_new_of_positive_magnitude p v hpos hz
  let w : Fin 13 → V := fun i => if i=11 then y else v (embed i)
  have hw : ∀ i, 0<w i := by
    intro i
    by_cases hi : i=11
    · simpa [w,hi] using hy
    · simpa [w,hi,oldIndex] using hv i
  exact ⟨fun i => w i-1,shifted_zero_of_positive hw hnew⟩

/-- The auxiliary norm forces a positive ordinate when its coefficient is
    at least two, without any lower bound on the other magnitude. -/
theorem ordinate_positive_of_norm {I z y : V} (hI : 2≤I)
    (hn : I*I*z*z+y*y=1+I*I*y*y) : 0<y := by
  apply pos_iff_ne_zero.mpr
  intro hy0
  have hp : I*I*z*z=1 := by simpa only [hy0,mul_zero,zero_mul,add_zero] using hn
  have hd : I*I∣(1:V) := ⟨z*z,by simpa only [mul_assoc] using hp.symm⟩
  have hle : I*I≤1 := Arithmetic.le_of_dvd (by simp) hd
  have hIle : I≤I*I := le_mul_of_one_le_right (by simp)
    (le_trans (by simp : (1:V)≤2) hI)
  exact (not_le_of_gt (lt_of_lt_of_le (by simp : (1:V)<2) hI)) (le_trans hIle hle)

/-- The displayed norm and signed residue suffice to recover the old natural
    witness from a positive direct-ordinate zero. -/
theorem new_positive_zero_to_old_natural_of_norm_residue
    (p : Fin 4 → ℤ) (v : Fin 14 → V) (I c R : V)
    (hv : ∀ i : Fin 13, 0<v (embed i)) (hI : 2≤I) (hR : 2≤R)
    (hhalf : 2*R<c) (hmod : SignMod c (magnitude (splitEval (signedV p) v)) R)
    (hn : I*I*magnitude (splitEval (signedV p) v)*magnitude (splitEval (signedV p) v)+
      v 11*v 11=1+I*I*(v 11)*(v 11))
    (hz : AdaptiveEquationSyntax2011.InternalZero (expressionAt86 p)
      (fun i => v (embed i))) :
    ∃ w : Fin 13 → V, AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveEquationSyntax2011.positiveShift
        (AdaptiveFirstRootFactor87Literal.expressionAt87 p)) w := by
  have hz2 := magnitude_ge_two hR hhalf hmod
  have hgap := ordinate_gt_magnitude hI hz2 hn
  exact new_positive_zero_to_old_natural_of_gap p v hv hgap hz

/-- The displayed auxiliary norm suffices to choose a positive direct
    ordinate from a positive old-expression zero. -/
theorem old_positive_zero_to_new_natural_of_aux_norm
    (p : Fin 4 → ℤ) (v : Fin 14 → V) (I z : V)
    (hv : ∀ i : Fin 13, 0<v (oldIndex i)) (hI : 2≤I)
    (hn : I*I*z*z+
      magnitude ((splitEval (signedV p) v).1+v 13,(splitEval (signedV p) v).2)*
        magnitude ((splitEval (signedV p) v).1+v 13,(splitEval (signedV p) v).2) =
      1+I*I*magnitude ((splitEval (signedV p) v).1+v 13,(splitEval (signedV p) v).2)*
        magnitude ((splitEval (signedV p) v).1+v 13,(splitEval (signedV p) v).2))
    (hz : AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveFirstRootFactor87Literal.expressionAt87 p) (fun i => v (oldIndex i))) :
    ∃ w : Fin 13 → V, AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveEquationSyntax2011.positiveShift (expressionAt86 p)) w := by
  have hp := ordinate_positive_of_norm hI hn
  exact old_positive_zero_to_new_natural_of_magnitude p v hv hp hz

end DiophantineConsistency.AdaptiveDirectOrdinate86Witness
