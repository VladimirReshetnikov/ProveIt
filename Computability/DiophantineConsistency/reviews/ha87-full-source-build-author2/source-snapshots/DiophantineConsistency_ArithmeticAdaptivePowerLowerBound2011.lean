import DiophantineConsistency.ArithmeticAdaptivePowerProjection2011

/-! The actual radix-47 port turns q | 3X into X ≥ 16. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptivePowerProjection2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pow_extends (r n : ℕ) (hn : n≠0) : r≤r^n := Nat.le_self_pow hn r

private theorem beta_lower_nat : 46≤CurrentMasks2011.beta := by
  have hr : 47≤CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; decide
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011 :=
    pow_extends _ _ (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_X_lower (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : 16≤v 6 := by
  have hb : (46:V)≤(CurrentMasks2011.beta:V) := by exact_mod_cast beta_lower_nat
  have hj : (1:V)≤v 0 := pos_iff_one_le.mp (hv 0)
  have hq : (47:V)≤1+v 0*(CurrentMasks2011.beta:V) := calc
    47=1+46 := by ring
    _≤1+v 0*(CurrentMasks2011.beta:V) := _root_.add_le_add (le_refl 1)
      (le_trans hb (le_mul_of_one_le_left (by simp) hj))
  have hp := (current_projection v hv hz).2
  have hp' : (47:V)≤3*v 6 := by
    apply le_trans hq
    simpa only [ArithmeticAdaptiveScaledNorms2011.currentPorts,Matrix.cons_val_zero] using hp
  by_contra hn
  have hx : v 6≤15 := lt_succ_iff_le.mp (by
    simpa only [show (15:V)+1=16 by ring] using lt_of_not_ge hn)
  have h3 : 3*v 6≤45 := by
    simpa only [show (3:V)*15=45 by ring] using mul_le_mul_of_nonneg_left hx (by simp : (0:V)≤3)
  exact (not_le_of_gt (by norm_num : (45:V)<47)) (le_trans hp' h3)

theorem current_natural_X_lower (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    16≤v 6+1 :=
  current_X_lower _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011
