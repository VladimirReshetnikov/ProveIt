import CompactRankResidueJoin
import CompactAuxPositiveCoordinates
import DiophantineConsistency.ArithmeticMaskPopulation

/-! A proposed twelve-coordinate free-J valuation, from the same compact
packing, outer seed parameters and auxiliary Pell witnesses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPositiveValuation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticMaskPopulation ArithmeticPellRecurrence
open CompactConstructedRank CompactRankResidueJoin CompactAuxPositiveCoordinates
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def valuation (K N s : V) (X : V → V) [𝚺₁-Function₁ X]
    (sY f auxT r eta zeta i auxw gamma : V) : Fin 12 → V :=
  let R := rank K N s X
  let Y := sY*Exp.exp (590069*N)^3
  let a := Exp.exp R*Y+Y
  ![rep 590069 N, Fw 590069 K N s X, alpha 590069 K N s X, f-1,
    auxT, Exp.exp R, Y, r, eta, zeta, delta a*i+auxw, gamma]

/-- Every coordinate of the proposed valuation is positive. `f` is the
auxiliary Pell abscissa for this exact rank and outer parameter. -/
theorem positive {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (hpack : PackingInput 590069 K low high N s X)
    (sY f auxT r eta zeta i auxw gamma : V)
    (hsY : 0 < sY) (hauxT : 0 < auxT) (hr : 0 < r) (heta : 0 < eta)
    (hzeta : 0 < zeta) (hi : 0 < i) (hauxw : 0 < auxw) (hgamma : 0 < gamma)
    (hf : let R := rank K N s X
      let Y := sY*Exp.exp (590069*N)^3
      let a := Exp.exp R*Y+Y
      f=xcoord (R*ycoord R a) a) :
    ∀ j, 0 < valuation K N s X sY f auxT r eta zeta i auxw gamma j := by
  have hN := N_pos hpack
  obtain ⟨v,hv⟩ := rep_eight (590069:V) N (by norm_num) hN
  have hJ : 0 < rep (590069:V) N := by rw [hv]; simp
  have hF := F_pos hpack
  have hA := (packing_alpha hpack).1
  let R := rank K N s X
  let Y := sY*Exp.exp (590069*N)^3
  let a := Exp.exp R*Y+Y
  have hR : 0 < R := lt_of_le_of_lt (by simp) (properties hpack).2.2
  have hcoord := auxiliary_f_pos a R (ycoord R a) f hR rfl hf
  have hY : 0 < Y := mul_pos hsY (pow_pos (exp_pos _) _)
  have hd : 0 < delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  have hn : 0 < delta a*i+auxw := add_pos_of_pos_of_nonneg (mul_pos hd hi) (by simp)
  intro j
  fin_cases j <;> simp only [valuation, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.cons_val_fin_one] <;>
    first | exact hJ | exact hF | exact hA | exact hcoord.2.2.1 | exact hauxT |
      exact exp_pos R | exact hY | exact hr | exact heta | exact hzeta | exact hn | exact hgamma

#print axioms CompactPositiveValuation.positive
end CompactPositiveValuation
