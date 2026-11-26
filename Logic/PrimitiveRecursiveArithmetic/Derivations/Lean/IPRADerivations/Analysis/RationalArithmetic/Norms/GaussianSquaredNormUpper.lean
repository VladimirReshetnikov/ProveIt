import IPRADerivations.Analysis.Names.GaussianLinearDistanceName
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowers

/-!
# Taking the norm bound from an actual squared comparison

The comparison of the actual squared norm with `(S/T)^2+(A/B)^2`
implies an ordinary norm bound of `S/T+A/B`. The proof works on the
decoded fractions and requires no square-root operation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSquaredNormUpper

open_ipra
open GaussianRationalMetric (bounded qnormSq squaredTolerance squared_tolerance_represents qnormSq_represents bounded_iff)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem bound_of_represented_squared_upper (z c S T A B : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat (S*S)) (T*T))
    (h : Γ ⊢[PRAAx] upper (qnormSq z) c (A*A) (B*B)) :
    Γ ⊢[PRAAx] bounded z (S*B+A*T) (T*B) := by
  let E := rawDen z
  let w := rawGaussian z
  have hE : Γ ⊢[PRAAx] le one E := raw_den_positive z
  have ht := qnormSq_represents z w E hE (raw_represents z)
  have cleared := GaussianLinearDistanceName.upper_to_cleared _ _ _ _ _ _ _ _ ht hc h
  apply (bounded_iff z w E (S*B+A*T) (T*B) hE (positive_product T B hT hB) (raw_represents z)).iffMpr
  apply le_trans (le_congr (by ipra_ring) (.eqRefl _) cleared)
  exact le_of_eq_add (d := two*(S*B)*(A*T)*(E*E)) (by ipra_ring)

theorem bound_of_squared_upper (z S T A B : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper (qnormSq z) (squaredTolerance S T) (A*A) (B*B)) :
    Γ ⊢[PRAAx] bounded z (S*B+A*T) (T*B) :=
  bound_of_represented_squared_upper z _ S T A B hT hB (squared_tolerance_represents S T hT) h

theorem bound_of_dyadic_squared_upper (z c S T p : PTm n) (hT : Γ ⊢[PRAAx] le one T)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat (S*S)) (T*T))
    (h : Γ ⊢[PRAAx] upper (qnormSq z) c one (unit (p+p))) :
    Γ ⊢[PRAAx] bounded z (S*unit p+T) (T*unit p) := by
  have shifted := upper_congr (.eqRefl _) (.eqRefl _) (one_mul one).eqSymm
    (pw_add two p p) h
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (bound_of_represented_squared_upper z c S T one (unit p) hT (unit_positive p) hc shifted)

theorem bound_of_power_squared_upper (z a b R p : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] upper (qnormSq z) (RationalNonnegativePowers.power a b (two*R)) one (unit (p+p))) :
    Γ ⊢[PRAAx] bounded z (pw a R*unit p+pw b R) (pw b R*unit p) := by
  have squarePower (t : PTm n) : Γ ⊢[PRAAx] pw t (two*R) ≐ pw t R*pw t R := by
    have e : Γ ⊢[PRAAx] two*R ≐ R+R := by ipra_ring
    exact (congrAp2 powF e (.eqRefl t)).eqTrans (pw_add t R R)
  exact bound_of_dyadic_squared_upper z _ (pw a R) (pw b R) p
    (RationalNonnegativePowers.denominator_positive b R hb)
    (GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simpa only [ZT.toZ_ofNat] using natEq (squarePower a)) (squarePower b)
      (RationalNonnegativePowers.power_represents a b (two*R) hb)) h

theorem actual_squared_norm_upper_to_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le one (var 4) ⟶
      upper (qnormSq (var 0)) (squaredTolerance (var 1) (var 2)) (var 3*var 3) (var 4*var 4) ⟶
      bounded (var 0) (var 1*var 4+var 3*var 2) (var 2*var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (bound_of_squared_upper _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSquaredNormUpper
