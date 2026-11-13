import P80NaturalForcedGamma
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only guard proof of J positivity for the natural 80 graph.
All declarations are unelaborated and require a represented positive K0. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80JPosDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Literal guard cut at J=0; K0 must be represented by `κ` in the model. -/
theorem guard_zero_cut (p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V) = ι κ) (hJ : v 0 = 0) :
    (P80NaturalForcedGamma.graph p).guardFactor.evalRing (fun j => ι (v j)) =
      -(ι (v 1) + ι (v 2) + 1) * (ι (v 6) + 1 + ι κ) - ι (v 1) := by
  simp [P80NaturalForcedGamma.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    hK, hJ, map_zero] <;> ring

/-- Strict K0 makes the guard at J=0 at most −2 in the difference ring. -/
theorem guard_at_most_negative_two (p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ) (hJ : v 0 = 0) :
    (P80NaturalForcedGamma.graph p).guardFactor.evalRing (fun j => ι (v j)) ≤ -2 := by
  rw [guard_zero_cut p κ v hK hJ]
  have h1 := ι_nonneg (v 1)
  have h2 := ι_nonneg (v 2)
  have h6 := ι_nonneg (v 6)
  have hkpos : (0 : DiffRing V) < ι κ := by
    simpa only [map_zero] using (ι_lt_ι.mpr hκ)
  have hkone : (1 : DiffRing V) ≤ ι κ :=
    ModelDifferenceRing.one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) hkpos
  have hm : 0 ≤ (ι (v 1) + ι (v 2)) * (ι (v 6) + ι κ - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hm]

/-- Zero forces slot J positive; all factor-unit work is local to the guard. -/
theorem J_pos_of_zero (p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)
    (hz : InternalZero (P80NaturalForcedGamma.graph p).output v) : 0 < v 0 := by
  apply pos_iff_ne_zero.mpr
  intro hJ
  have hg := guard_at_most_negative_two p κ v hK hκ hJ
  have hzring := (ModelDifferenceRing.internalZero_iff _ _).mp hz
  rw [P80NaturalForcedGamma.output_shape] at hzring
  simp only [Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_constant, Int.cast_one, Nat.cast_one] at hzring
  let P : DiffRing V := (P80NaturalForcedGamma.graph p).first.evalRing (fun j => ι (v j)) *
    (P80NaturalForcedGamma.graph p).main.evalRing (fun j => ι (v j)) *
    (P80NaturalForcedGamma.graph p).aux.evalRing (fun j => ι (v j)) *
    (P80NaturalForcedGamma.graph p).strong.evalRing (fun j => ι (v j))
  let G : DiffRing V := (P80NaturalForcedGamma.graph p).guardFactor.evalRing (fun j => ι (v j))
  have hp : P*G = 1 := by dsimp [P,G]; exact sub_eq_zero.mp hzring
  have hG : G ≤ -2 := hg
  have hpneg : P < 0 := by
    by_contra h
    have hp0 : 0 ≤ P := le_of_not_gt h
    have hn := mul_nonpos_of_nonneg_of_nonpos hp0 (show G ≤ 0 by linarith)
    linarith
  have hpone : (1 : DiffRing V) ≤ -P :=
    ModelDifferenceRing.one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) (neg_pos.mpr hpneg)
  have hm : 0 ≤ (-P-1)*(-G-2) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hm]

end DiophantineConsistency.Natural80JPosDraft

#print axioms DiophantineConsistency.Natural80JPosDraft.J_pos_of_zero
