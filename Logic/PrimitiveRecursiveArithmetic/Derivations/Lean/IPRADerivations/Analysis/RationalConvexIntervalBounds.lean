import IPRADerivations.Analysis.RationalNestedIntervals
import IPRADerivations.Analysis.RationalMultiplicativeConvexity
import IPRADerivations.Core.LinearCombination

/-!
# Finite secants from the original interval comparisons

At one precision, the midpoint is at most half a width from either
endpoint. Exact ordinary convexity from lower to upper endpoints thus
gives the two actual centered-sampler secant comparisons, with the
original full width as tolerance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexIntervalBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)
open RationalArgmin (rationalLE rationalLE_congr transitive reflexive denominator_positive left)
open RationalArithmetic (add multiply)
open RationalSupMetric (denominatorOf numeratorOf)
open RationalConvexSecants (scale within affine)
open RationalConvexFiniteModulus (eps power_positive)
open RationalConvexEndpointBudget (order_of_upper)
open RationalCubeMidpoint (fraction fraction_represents)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_add add_monotone)
open RationalAlgebra (add_associative add_commutative add_congr multiply_commutative multiply_congr multiply_add)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def halfWidth (p : PTm n) : PTm n := fraction one (two*pw two p)

theorem scale_monotone (a q r : PTm n) (h : Γ ⊢[PRAAx] rationalLE q r) :
    Γ ⊢[PRAAx] rationalLE (scale a q) (scale a r) := by
  let A := denominatorOf q
  let B := denominatorOf r
  have hA := denominator_positive (Γ := Γ) q
  have hB := denominator_positive (Γ := Γ) r
  have rq := RationalRepresentations.represents_multiply (Γ := Γ) (natCode a) q _ _ one A
    (natCode_represents a) (RationalRepresentations.represents_self q)
  have rr := RationalRepresentations.represents_multiply (Γ := Γ) (natCode a) r _ _ one B
    (natCode_represents a) (RationalRepresentations.represents_self r)
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ rq rr
    (RationalAlgebra.positive_product (le_refl one) hA)
    (RationalAlgebra.positive_product (le_refl one) hB)
  apply zle_of_toZ (a*monus (left r q) (left q r))
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at e ⊢
  dsimp only [A,B]
  ipra_simps
  linear_combination -𝔟 a*e

theorem scale_add (a q r : PTm n) : Γ ⊢[PRAAx] scale a (add q r) ≐ add (scale a q) (scale a r) :=
  multiply_add (natCode a) q r

theorem scale_add_weights (a b q : PTm n) : Γ ⊢[PRAAx] scale (a+b) q ≐ add (scale a q) (scale b q) := by
  have first := multiply_congr (natCode_add (Γ := Γ) a b).eqSymm (.eqRefl q)
  exact first.eqTrans ((multiply_commutative _ q).eqTrans ((multiply_add q (natCode a) (natCode b)).eqTrans
    (add_congr (multiply_commutative q (natCode a)) (multiply_commutative q (natCode b)))))

theorem half_width_positive (p : PTm n) : Γ ⊢[PRAAx] le one (two*pw two p) :=
  RationalAlgebra.positive_product (le_succ_self one) (power_positive p)

theorem half_width_twice (p : PTm n) : Γ ⊢[PRAAx] add (halfWidth p) (halfWidth p) ≐ eps p := by
  have h := half_width_positive (Γ := Γ) p
  have e := power_positive (Γ := Γ) p
  have r := fraction_represents one (two*pw two p) h
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ e)
    (RationalRepresentations.represents_add _ _ _ _ _ _ r r) (fraction_represents one _ e)
    (RationalAlgebra.positive_product h h) e
  ipra_lc

private theorem add_shuffle (a b c d : PTm n) : Γ ⊢[PRAAx] add (add a b) (add c d) ≐ add (add a c) (add b d) :=
  (add_associative a b (add c d)).eqTrans
    ((add_congr (.eqRefl a) (add_associative b c d).eqSymm).eqTrans
      ((add_congr (.eqRefl a) (add_congr (add_commutative b c) (.eqRefl d))).eqTrans
        ((add_congr (.eqRefl a) (add_associative c b d)).eqTrans (add_associative a c (add b d)).eqSymm)))

theorem affine_half_width (a b X Y p : PTm n) : Γ ⊢[PRAAx]
    add (RationalMultiplicativeConvexity.weighted a b (add X (halfWidth p)) (add Y (halfWidth p)))
      (scale (a+b) (halfWidth p)) ≐ affine a b (a+b) X Y (eps p) := by
  let H := halfWidth p
  have e : Γ ⊢[PRAAx] RationalMultiplicativeConvexity.weighted a b (add X H) (add Y H) ≐
      add (add (scale a X) (scale b Y)) (scale (a+b) H) :=
    (add_congr (scale_add a X H) (scale_add b Y H)).eqTrans
      ((add_shuffle (scale a X) (scale a H) (scale b Y) (scale b H)).eqTrans
        (add_congr (.eqRefl _) (scale_add_weights a b H).eqSymm))
  exact (add_congr e (.eqRefl _)).eqTrans ((add_associative _ _ _).eqTrans
    (add_congr (.eqRefl _) ((scale_add (a+b) H H).eqSymm.eqTrans
      (multiply_congr (.eqRefl _) (half_width_twice p)))))

/-- Multiplicative convexity yields this exact rational arithmetic inequality
with one full input width as tolerance for the same three midpoints. -/
theorem centered_secant (a b LX UX LY UY LZ UZ p : PTm n)
    (hx : Γ ⊢[PRAAx] RationalValueBounds.upper UX LX one (pw two p))
    (hy : Γ ⊢[PRAAx] RationalValueBounds.upper UY LY one (pw two p))
    (hz : Γ ⊢[PRAAx] RationalValueBounds.upper UZ LZ one (pw two p))
    (hc : Γ ⊢[PRAAx] RationalMultiplicativeConvexity.ordinary a b UX UY LZ) :
    Γ ⊢[PRAAx] within (a+b) b a (midpoint LX UX) (midpoint LZ UZ) (midpoint LY UY) (eps p) := by
  let X := midpoint LX UX
  let Y := midpoint LY UY
  let Z := midpoint LZ UZ
  let H := halfWidth p
  let w := a+b
  have hH := half_width_positive (Γ := Γ) p
  have ex : Γ ⊢[PRAAx] rationalLE UX (add X H) :=
    order_of_upper _ _ _ _ hH (RationalCubeInfimumName.midpoint_half_right _ _ _ _ hx)
  have ey : Γ ⊢[PRAAx] rationalLE UY (add Y H) :=
    order_of_upper _ _ _ _ hH (RationalCubeInfimumName.midpoint_half_right _ _ _ _ hy)
  have ez : Γ ⊢[PRAAx] rationalLE Z (add LZ H) :=
    order_of_upper _ _ _ _ hH (RationalCubeInfimumName.midpoint_half_left _ _ _ _ hz)
  have L := rationalLE_congr (.eqRefl _) (scale_add w LZ H) (scale_monotone w Z (add LZ H) ez)
  have R := add_monotone _ _ _ _ (scale_monotone a UX (add X H) ex) (scale_monotone b UY (add Y H) ey)
  have middle := add_monotone _ _ _ _ (transitive hc R) (reflexive (scale w H))
  exact transitive L (rationalLE_congr (.eqRefl _) (affine_half_width a b X Y p) middle)

theorem actual_centered_secant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((RationalValueBounds.upper (var 3) (var 2) one (pw two (var 8)) ⋏
      (RationalValueBounds.upper (var 5) (var 4) one (pw two (var 8)) ⋏
        RationalValueBounds.upper (var 7) (var 6) one (pw two (var 8)))) ⟶
      RationalMultiplicativeConvexity.ordinary (var 0) (var 1) (var 3) (var 5) (var 6) ⟶
      within (var 0+var 1) (var 1) (var 0) (midpoint (var 2) (var 3)) (midpoint (var 6) (var 7))
        (midpoint (var 4) (var 5)) (eps (var 8))) :=
  closeUniv 9 (.impI (.impI (centered_secant _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalConvexIntervalBounds
