import IPRADerivations.Analysis.RationalConvexSecants
import IPRADerivations.Analysis.RationalNonnegativePowers
import IPRADerivations.Analysis.WeightedAMGM

/-!
# Multiplicative convexity on rational interval endpoints

The lower and upper endpoint codes may use different denominators. Their
actual rational powers preserve the value of a nonnegative representative,
and a common positive denominator reflects the multiplicative hypothesis
into the checked finite weighted AM–GM derivation. The result is the exact
ordinary convexity inequality for the same endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMultiplicativeConvexity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (pred)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open RationalArgmin (rationalLE reflexive denominator_positive)
open RationalArithmetic (represents add multiply)
open RationalSupMetric (denominatorOf)
open RationalConvexSecants (nonnegative naturalNumerator nonnegative_representation rescaled_representation
  multiply_natural_representation add_natural_representation compare_same_to_natural compare_same_from_natural)
open GaussianRationalHorner (scalar_congr)
open GaussianRationalMetric (comparison_to_cleared)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def power (q k : PTm n) : PTm n :=
  RationalNonnegativePowers.power (naturalNumerator q) (denominatorOf q) k
def weighted (a b X Y : PTm n) : PTm n := add (RationalConvexSecants.scale a X) (RationalConvexSecants.scale b Y)
def multiplicative (a b X Y Z : PTm n) : Fm PTm n :=
  rationalLE (power Z (a+b)) (multiply (power X a) (power Y b))
def ordinary (a b X Y Z : PTm n) : Fm PTm n :=
  rationalLE (RationalConvexSecants.scale (a+b) Z) (weighted a b X Y)

theorem natural_representation_cross (q A D B E : PTm n)
    (ha : Γ ⊢[PRAAx] represents q (ZT.ofNat A) D) (hb : Γ ⊢[PRAAx] represents q (ZT.ofNat B) E) :
    Γ ⊢[PRAAx] A*E ≐ B*D := by
  have one := comparison_to_cleared q q A B D E ha hb (reflexive q)
  have two := comparison_to_cleared q q B A E D hb ha (reflexive q)
  exact le_antisymm (le_congr (mul_comm _ _) (.eqRefl _) one) (le_congr (mul_comm _ _) (.eqRefl _) two)

theorem power_representation (q A D k : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] represents q (ZT.ofNat A) D) :
    Γ ⊢[PRAAx] represents (power q k) (ZT.ofNat (pw A k)) (pw D k) := by
  let a := naturalNumerator q
  let d := denominatorOf q
  have hd := denominator_positive (Γ := Γ) q
  have e := natural_representation_cross q a d A D (nonnegative_representation q hq) hr
  have ee : Γ ⊢[PRAAx] pw a k*pw D k ≐ pw A k*pw d k :=
    (pw_mul_base a D k).eqSymm.eqTrans ((congrAp2 powF (.eqRefl k) e).eqTrans (pw_mul_base A d k))
  have u := RationalNonnegativePowers.power_represents a d k hd
  have v := RationalNonnegativePowers.power_represents A D k hD
  have eq : Γ ⊢[PRAAx] power q k ≐ RationalNonnegativePowers.power A D k := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNonnegativePowers.power_canonical a d k hd)
      (RationalNonnegativePowers.power_canonical A D k hD) u v
      (RationalNonnegativePowers.denominator_positive d k hd)
      (RationalNonnegativePowers.denominator_positive D k hD)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    simpa only [Q.mk_mul,map_mul] using natEq ee
  exact scalar_congr eq.eqSymm (ZT.derive rfl) (.eqRefl _) v

theorem product_representation (X Y u v D a b : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hx : Γ ⊢[PRAAx] nonnegative X) (hy : Γ ⊢[PRAAx] nonnegative Y)
    (rx : Γ ⊢[PRAAx] represents X (ZT.ofNat u) D) (ry : Γ ⊢[PRAAx] represents Y (ZT.ofNat v) D) :
    Γ ⊢[PRAAx] represents (multiply (power X a) (power Y b)) (ZT.ofNat (pw u a*pw v b)) (pw D (a+b)) := by
  have h := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (power_representation X u D a hx hD rx) (power_representation Y v D b hy hD ry)
  refine scalar_congr (.eqRefl _) ?_ (pw_add D a b).eqSymm h
  apply ZT.derive
  simp only [ZT.toZ_ofNat,ZT.toZ_mul,Q.mk_mul,map_mul]

theorem natural_weighted_convexity (a b u v z : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] le (pw z (a+b)) (pw u a*pw v b)) :
    Γ ⊢[PRAAx] le ((a+b)*z) (a*u+b*v) := by
  have ea := RationalIntegerNormalization.positive_form ha
  have et : Γ ⊢[PRAAx] a+b ≐ succ (pred a+b) := (congrAdd ea (.eqRefl b)).eqTrans (by ipra_ring)
  have hp := le_congr (congrAp2 powF et (.eqRefl z))
    (congrMul (congrAp2 powF ea (.eqRefl u)) (.eqRefl (pw v b))) h
  exact le_congr (congrMul et.eqSymm (.eqRefl z))
    (congrAdd (congrMul ea.eqSymm (.eqRefl u)) (.eqRefl _)) (WeightedAMGM.mult_convex hp)

theorem multiplicative_to_ordinary (a b X Y Z : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hx : Γ ⊢[PRAAx] nonnegative X) (hy : Γ ⊢[PRAAx] nonnegative Y) (hz : Γ ⊢[PRAAx] nonnegative Z)
    (h : Γ ⊢[PRAAx] multiplicative a b X Y Z) : Γ ⊢[PRAAx] ordinary a b X Y Z := by
  let U := denominatorOf X
  let V := denominatorOf Y
  let W := denominatorOf Z
  let D := U*V*W
  have hD : Γ ⊢[PRAAx] le one D := RationalAlgebra.positive_product
    (RationalAlgebra.positive_product (denominator_positive X) (denominator_positive Y)) (denominator_positive Z)
  have rx := rescaled_representation X (V*W) D hx (by dsimp [U,V,W,D]; ipra_ring)
  have ry := rescaled_representation Y (U*W) D hy (by dsimp [U,V,W,D]; ipra_ring)
  have rz := rescaled_representation Z (U*V) D hz (by dsimp [U,V,W,D]; ipra_ring)
  have hp := compare_same_to_natural _ _ _ _ (pw D (a+b))
    (RationalNonnegativePowers.denominator_positive D (a+b) hD)
    (power_representation Z _ D (a+b) hz hD rz)
    (product_representation X Y _ _ D a b hD hx hy rx ry) h
  exact compare_same_from_natural _ _ _ _ D hD (multiply_natural_representation (a+b) Z _ D rz)
    (add_natural_representation _ _ _ _ D hD (multiply_natural_representation a X _ D rx)
      (multiply_natural_representation b Y _ D ry)) (natural_weighted_convexity a b _ _ _ ha hp)

theorem actual_rational_multiplicative_convexity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ (nonnegative (var 2) ⋏ (nonnegative (var 3) ⋏ nonnegative (var 4))) ⟶
      multiplicative (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      ordinary (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (multiplicative_to_ordinary _ _ _ _ _ hyp2
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalMultiplicativeConvexity
