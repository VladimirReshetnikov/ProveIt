import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.GaussianGammaGaussShiftedProduct
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedFiniteProductApartness
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaC9Bound

/-!
# Uniform separation for the shifted Gamma product

Each returned Gamma sample is exactly the canonical reciprocal of a
nonzero reciprocal-Gamma tail sample. The numerical C9 majorant bounds
that tail uniformly over all row indices. The finite product then
inherits an explicit separation denominator and an inversion clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussShiftedApartness

open_ipra
open ComplexLogarithmRemainder (oneCode normSq_one)
open GaussianGammaC9Bound (exponentialMajorant majorant)
open GaussianGammaGaussShiftedProduct (source rowF rowData rowRadius nameF data)
open GaussianGammaReciprocalInverse (gammaF gammaData gammaHeight original_gamma_inverse)
open GaussianNameReciprocal (lower apart input)
open GaussianNamedFiniteProductApartness (rowLower rowLowerAt)
open GaussianRationalHorner (positive_product canonical_unique ofGaussian_represents)
open GaussianRationalL1 (raw_den_positive raw_represents)
open GaussianRationalMetric (bounded)
open GaussianRationalLowerBounds (lower_from_representation)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone reciprocal reciprocal_canonical reciprocal_identity)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowDenominator (R : PTm n) : PTm n := majorant (R+one)

def apartClock (R m : PTm n) : PTm n := GaussianNamedFiniteProductApartness.apartClock m (rowDenominator R)

ipra_subst rowDenominator [one]

ipra_subst apartClock

theorem majorant_positive (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx] le one (majorant R) := by
  have front := positive_product R (pw (one+R) (two*R)) hR
    (GaussianFactorBudget.power_positive _ _ (le_add_right one R))
  have exp : Γ ⊢[PRAAx] le one (exponentialMajorant R) :=
    GaussianFactorBudget.power_positive _ _ (le_of_eq_add (d := two) (by ipra_ring))
  exact positive_product _ _ front exp

theorem row_denominator_positive (R : PTm n) : Γ ⊢[PRAAx] le one (rowDenominator R) :=
  majorant_positive (R+one) (le_add_left one R)

private theorem unit_lower : Γ ⊢[PRAAx] lower (qone : PTm n) one :=
  lower_from_representation _ oneCode one one one (le_refl _) (le_refl _) (ofGaussian_represents _ _ (le_refl _))
    (le_congr (by ipra_ring) (congrMul (.eqRefl _) normSq_one).eqSymm (le_refl _))

theorem gamma_observation_lower (p z R B a d : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d) :
    Γ ⊢[PRAAx] lower (ap2 gammaF p (gammaData z R B d)) (majorant R) := by
  let f := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let H := gammaHeight z R B d
  let t := GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus H) p
  let y := GaussianNameReciprocal.tail f H x t
  let v := reciprocal y
  have hi := (original_gamma_inverse z R B a d h).andE₁
  have tailLower := GaussianNameReciprocal.tail_lower f H x t hi.andE₁ hi.andE₂
  have positiveNorm := GaussianNameReciprocal.lower_norm_positive y _ (GaussianNameReciprocal.R_positive H) tailLower
  have recoded : Γ ⊢[PRAAx] GaussianFastValueCut.recode v ≐ v :=
    canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical v) (reciprocal_canonical y)
      (raw_den_positive v) (GaussianFastValueCut.recode_represents v) (raw_represents v)
  have read : Γ ⊢[PRAAx] ap2 gammaF p (gammaData z R B d) ≐ v :=
    (GaussianNameReciprocal.name_at f H x p).eqTrans recoded
  have hy : Γ ⊢[PRAAx] bounded y (majorant R) one :=
    GaussianGammaC9Bound.reciprocal_sample_bound (t+GaussianNameReciprocal.anchor H) z R B h.andE₁
  have exactInv := (qmul_commutative v y).eqTrans (reciprocal_identity y positiveNorm)
  have productLower := GaussianRationalLowerBounds.lower_congr exactInv.eqSymm (.eqRefl _) (.eqRefl _) unit_lower
  have lowerV := GaussianBoundedInverseApartness.factor_lower v y one one (majorant R) (le_refl one)
    (majorant_positive R h.andE₁.andE₁) productLower hy
  exact GaussianRationalLowerBounds.lower_congr read.eqSymm (.eqRefl _) (one_mul _) lowerV

theorem row_lower_at (p r z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] lower (ap3 rowF p r (rowData z R B m d)) (rowDenominator R) :=
  GaussianNameReciprocal.lower_congr (GaussianGammaGaussShiftedProduct.row_at p r z R B m d).eqSymm (.eqRefl _)
    (gamma_observation_lower p _ _ _ _ _ (GaussianGammaGaussShiftedProduct.row_source z R B m r a d h hr))

theorem row_lower (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] rowLower rowF m (rowDenominator R) (rowData z R B m d) := by
  refine .allI (.allI (.impI ?_))
  let lift (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := lt (var 0) (lift m) :: (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using h.shift.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (lift m) := Prf.hyp0
  simpa [Δ,lift,rowLower,rowLowerAt,Syn.shift] using
    row_lower_at (var 1) (var 0) (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) hs hr

theorem name_lower (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data z R B m d)) (GaussianNamedFiniteProductApartness.denominator (rowDenominator R) m) :=
  GaussianNamedFiniteProductApartness.name_lower rowF p m (rowRadius R m d) one (rowDenominator R) (rowData z R B m d)
    (row_denominator_positive R) (row_lower z R B m a d h)

theorem name_apart (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] apart nameF (apartClock R m) (data z R B m d) :=
  GaussianNamedFiniteProductApartness.name_apart rowF m (rowRadius R m d) one (rowDenominator R) (rowData z R B m d)
    (row_denominator_positive R) (row_lower z R B m a d h)

theorem name_input (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] input nameF (apartClock R m) (data z R B m d) :=
  .andI (GaussianGammaGaussShiftedProduct.name_regular z R B m a d h) (name_apart z R B m a d h)

theorem actual_Gauss_shifted_product_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      input nameF (apartClock (var 1) (var 3)) (data (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (name_input _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussShiftedApartness
