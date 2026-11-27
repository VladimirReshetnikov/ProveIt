import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerAlgebra

/-!
# Reflecting rational norm contraction through an actual inverse

The exact normalized product a*b=1 supplies an actual roundtrip for
canonical original points. Multiplication by the derived nonnegative
qnormSq(a), norm multiplicativity, and literal scalar associativity then
reflect a contraction through b. No norm positivity or cancellation law
is assumed, and the original scalar r may be raw, negative, or zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalInvertibleNorm

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.RationalArithmetic (multiply)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem norm_nonnegative (a : PTm n) : Γ ⊢[PRAAx]
    le (RationalSupMetric.numeratorOf (qnormSq a)).neg (RationalSupMetric.numeratorOf (qnormSq a)).pos :=
  GaussianRationalL1.nonnegative_of_representation _ _ _
    (positive_product _ _ (raw_den_positive a) (raw_den_positive a))
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive a) (raw_represents a))

theorem qmul_roundtrip (a b u : PTm n) (hInverse : Γ ⊢[PRAAx] qmul a b ≐ qone)
    (hu : Γ ⊢[PRAAx] canonical u) : Γ ⊢[PRAAx] qmul a (qmul b u) ≐ u :=
  (GaussianReciprocalHorner.qmul_associative a b u).eqSymm.eqTrans
    ((qmul_congr hInverse (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone u).eqTrans
        (GaussianReciprocalHorner.qmul_one_right u hu)))

theorem norm_roundtrip (a b u : PTm n) (hInverse : Γ ⊢[PRAAx] qmul a b ≐ qone)
    (hu : Γ ⊢[PRAAx] canonical u) : Γ ⊢[PRAAx]
    multiply (qnormSq a) (qnormSq (qmul b u)) ≐ qnormSq u :=
  (GaussianRationalProductWitness.norm_multiply a (qmul b u)).eqSymm.eqTrans
    (GaussianRationalProductWitness.qnormSq_congr (qmul_roundtrip a b u hInverse hu))

theorem commute_multiplier (a r c : PTm n) : Γ ⊢[PRAAx]
    multiply a (multiply r c) ≐ multiply r (multiply a c) :=
  (RationalAlgebra.multiply_associative a r c).eqSymm.eqTrans
    ((RationalAlgebra.multiply_congr (RationalAlgebra.multiply_commutative a r) (.eqRefl _)).eqTrans
      (RationalAlgebra.multiply_associative r a c))

/-- The invertibility hypothesis is a genuine literal arithmetic identity.
The only order multiplication is by a derived nonnegative actual norm. -/
theorem reflect_contraction (a b u v r : PTm n)
    (hInverse : Γ ⊢[PRAAx] qmul a b ≐ qone)
    (hu : Γ ⊢[PRAAx] canonical u) (hv : Γ ⊢[PRAAx] canonical v)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq (qmul b u)) (multiply r (qnormSq (qmul b v)))) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq u) (multiply r (qnormSq v)) := by
  have scaled := RationalArithmetic.multiply_monotone _ _ _ (norm_nonnegative (Γ := Γ) a) h
  have left := norm_roundtrip a b u hInverse hu
  have right : Γ ⊢[PRAAx] multiply (qnormSq a) (multiply r (qnormSq (qmul b v))) ≐ multiply r (qnormSq v) :=
    (commute_multiplier _ _ _).eqTrans (RationalAlgebra.multiply_congr (.eqRefl _) (norm_roundtrip a b v hInverse hv))
  exact RationalArgmin.rationalLE_congr left right scaled

/-- Forward transport uses no inverse, positivity, or canonical-input guard. -/
theorem preserve_contraction (b u v r : PTm n)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq u) (multiply r (qnormSq v))) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (qmul b u)) (multiply r (qnormSq (qmul b v))) := by
  have scaled := RationalArithmetic.multiply_monotone _ _ _ (norm_nonnegative (Γ := Γ) b) h
  exact RationalArgmin.rationalLE_congr (GaussianRationalProductWitness.norm_multiply b u).eqSymm
    ((commute_multiplier _ _ _).eqTrans
      (RationalAlgebra.multiply_congr (.eqRefl _) (GaussianRationalProductWitness.norm_multiply b v).eqSymm)) scaled

theorem rational_inverse_roundtrip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qmul (var 0) (var 1) ≐ qone ⟶ canonical (var 2) ⟶ qmul (var 0) (qmul (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.impI (.impI (qmul_roundtrip _ _ _ Prf.hyp1 Prf.hyp0)))
theorem rational_invertible_contraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (qmul (var 0) (var 1) ≐ qone ⟶ canonical (var 2) ⟶ canonical (var 3) ⟶
      RationalArgmin.rationalLE (qnormSq (qmul (var 1) (var 2))) (multiply (var 4) (qnormSq (qmul (var 1) (var 3)))) ⟶
        RationalArgmin.rationalLE (qnormSq (var 2)) (multiply (var 4) (qnormSq (var 3)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (reflect_contraction _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem rational_scaled_contraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (RationalArgmin.rationalLE (qnormSq (var 1)) (multiply (var 3) (qnormSq (var 2))) ⟶
      RationalArgmin.rationalLE (qnormSq (qmul (var 0) (var 1))) (multiply (var 3) (qnormSq (qmul (var 0) (var 2))))) :=
  closeUniv 4 (.impI (preserve_contraction _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalInvertibleNorm
