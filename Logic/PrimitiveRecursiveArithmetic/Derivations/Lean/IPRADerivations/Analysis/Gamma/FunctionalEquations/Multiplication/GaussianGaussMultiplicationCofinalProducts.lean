import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.GaussianGaussMultiplicationCofinalRows
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedBoundedProductObservation

/-!
# Convergence of the two products in the cleared Gauss identity

Both literal cofinal products are compared to the original named
limits with budgets independent of the cutoff. The limit of the
finite unit Gamma factor is the canonical one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationCofinalProducts

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGaussMultiplicationCofinalRows
  (shiftedSample unitSample powerSample scaledSample referenceSample scaledData)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev leftF : PR 2 := GaussianGammaGaussShiftedProduct.nameF
abbrev referenceF : PR 2 := GaussianGammaGaussReferenceProduct.nameF
abbrev innerF : PR 2 := multiplyF powerF gammaF
abbrev rightF : PR 2 := multiplyF innerF referenceF

def leftData (z R B m d : PTm n) : PTm n := GaussianGammaGaussShiftedProduct.data z R B m d
def referenceData (m : PTm n) : PTm n := GaussianGammaGaussReferenceProduct.data m
def innerData (z R B m d : PTm n) : PTm n :=
  multiplyData powerF gammaF (limitData z R B m) (scaledData z R B m d)
def rightData (z R B m d : PTm n) : PTm n :=
  multiplyData innerF referenceF (innerData z R B m d) (referenceData m)

def leftRaw (p z R B m a d : PTm n) : PTm n :=
  qmul (shiftedSample p z R B m a d) (unitSample p R m a d)
def rightRaw (p z R B m a d : PTm n) : PTm n :=
  qmul (qmul (powerSample p z R B m a d) (scaledSample p z R B m a d)) (referenceSample p R m a d)

def powerBound (z R B m : PTm n) : PTm n := U powerF (limitData z R B m)
def scaledBound (z R B m d : PTm n) : PTm n := U gammaF (scaledData z R B m d)
def referenceBound (m : PTm n) : PTm n := U referenceF (referenceData m)
def shiftedBound (z R B m d : PTm n) : PTm n := U leftF (leftData z R B m d)
def finiteReferenceBound (m : PTm n) : PTm n :=
  GaussianNamedFiniteProduct.radius (GaussianGammaGaussReferenceEulerProduct.rowRadius m) m
def leftBudget (z R B m d : PTm n) : PTm n :=
  (two*GaussianGammaGaussEulerProduct.errorBudget R m d)*(num 4+one)+shiftedBound z R B m d*num 4
def innerBudget (z R B m d : PTm n) : PTm n :=
  num 3*(two+scaledBound z R B m d)+powerBound z R B m*two
def rightRawBudget (z R B m d : PTm n) : PTm n :=
  innerBudget z R B m d*finiteReferenceBound m+
    (powerBound z R B m*scaledBound z R B m d)*(two*GaussianGammaGaussReferenceEulerProduct.errorBudget m)
def rightNameBudget (z R B m d : PTm n) : PTm n :=
  two*(powerBound z R B m*scaledBound z R B m d+referenceBound m)+
    (two*(powerBound z R B m+scaledBound z R B m d))*referenceBound m
def rightBudget (z R B m d : PTm n) : PTm n := rightRawBudget z R B m d+rightNameBudget z R B m d

ipra_subst leftData
ipra_subst rightData [innerData, referenceData]
ipra_subst leftRaw
ipra_subst rightRaw
ipra_subst leftBudget [shiftedBound, one, two]
ipra_subst rightBudget [rightRawBudget, rightNameBudget, innerBudget, finiteReferenceBound, powerBound, scaledBound, referenceBound, referenceData, two]

theorem left_regular (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] pointCN leftF (leftData z R B m d) :=
  GaussianGammaGaussShiftedProduct.name_regular z R B m a d h

theorem right_regular (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] pointCN rightF (rightData z R B m d) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _
      (GaussianGaussMultiplicationCofinalRows.limit_power_regular z R B m a d h)
      (GaussianGaussMultiplicationCofinalRows.scaled_regular z R B m a d h))
    (GaussianGammaGaussReferenceProduct.name_regular m)

private theorem bounded_near (u v A B p : PTm n)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A (unit p)) (hv : Γ ⊢[PRAAx] bounded v B one) :
    Γ ⊢[PRAAx] bounded u (A+B) one := by
  have hp := unit_positive (Γ := Γ) p
  have stable := distance_radius_mono _ _ _ _ A one hp (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right A hp)) hd
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (one_mul _)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) stable hv)

theorem left_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (leftRaw p z R B m a d) (ap2 leftF p (leftData z R B m d)) (leftBudget z R B m d) (unit p) := by
  let x := ap2 leftF p (leftData z R B m d)
  let u := unitSample p R m a d
  have hm := h.andE₁.andE₁
  have err := GaussianGaussMultiplicationCofinalRows.unit_error p R m a d hm
  have hb := bounded_near u qone (num 4) one p err GaussianRationalReciprocal.qone_bounded
  have bound := GaussianNameBounds.sample_bound leftF (leftData z R B m d) p (left_regular z R B m a d h)
  have hc := GaussianRationalHorner.canonical_congr (GaussianGammaGaussShiftedProduct.name_at (Γ := Γ) p z R B m d)
    (GaussianNamedFiniteProduct.sample_canonical _ _ _ _)
  have eq := (GaussianNameRingLaws.multiply_one_recode x).eqTrans (GaussianExponentialReference.recode_fixed x hc)
  exact distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ _ _ (unit p) (num 4+one) (shiftedBound z R B m d)
      (unit_positive p) (GaussianGaussMultiplicationCofinalRows.shifted_error p z R B m a d h) err hb bound)

private theorem raw_right_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (rightRaw p z R B m a d)
      (qmul (qmul (ap2 powerF p (limitData z R B m)) (ap2 gammaF p (scaledData z R B m d)))
        (ap2 referenceF p (referenceData m))) (rightRawBudget z R B m d) (unit p) := by
  let w := ap2 powerF p (limitData z R B m)
  let g := ap2 gammaF p (scaledData z R B m d)
  let aG := scaledSample p z R B m a d
  let aR := referenceSample p R m a d
  let W := powerBound z R B m
  let G := scaledBound z R B m d
  have hm := h.andE₁.andE₁
  have hW : Γ ⊢[PRAAx] bounded w W one := GaussianNameBounds.sample_bound _ _ _
    (GaussianGaussMultiplicationCofinalRows.limit_power_regular z R B m a d h)
  have hG : Γ ⊢[PRAAx] bounded g G one := GaussianNameBounds.sample_bound _ _ _
    (GaussianGaussMultiplicationCofinalRows.scaled_regular z R B m a d h)
  have ge := GaussianGaussMultiplicationCofinalRows.scaled_error p z R B m a d h
  have finiteG := bounded_near aG g two G p ge hG
  have finiteR : Γ ⊢[PRAAx] bounded aR (finiteReferenceBound m) one :=
    GaussianGammaGaussReferenceEulerProduct.sample_bound p m _ (GaussianGaussMultiplicationCofinalRows.reference_cutoff p R m a d hm)
  have product := GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (GaussianRationalReciprocal.bounded_product w g W one G one (le_refl one) (le_refl one) hW hG)
  have middle : Γ ⊢[PRAAx] distanceBounded (qmul (powerSample p z R B m a d) aG) (qmul w g) (innerBudget z R B m d) (unit p) :=
    GaussianNameArithmetic.product_distance _ _ _ _ (num 3) two (unit p) (two+G) W (unit_positive p)
      (GaussianGaussMultiplicationCofinalRows.power_error p z R B m a d h) ge finiteG hW
  exact GaussianNameArithmetic.product_distance _ _ _ _ _ _ (unit p) _ _ (unit_positive p) middle
    (GaussianGaussMultiplicationCofinalRows.reference_error p R m a d hm) finiteR product

private theorem named_right_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rightF p (rightData z R B m d))
      (qmul (qmul (ap2 powerF p (limitData z R B m)) (ap2 gammaF p (scaledData z R B m d)))
        (ap2 referenceF p (referenceData m))) (rightNameBudget z R B m d) (unit p) := by
  let x := limitData z R B m
  let y := scaledData z R B m d
  let v := referenceData m
  let W := powerBound z R B m
  let G := scaledBound z R B m d
  let V := referenceBound m
  let i := innerData z R B m d
  have xN := GaussianGaussMultiplicationCofinalRows.limit_power_regular z R B m a d h
  have yN := GaussianGaussMultiplicationCofinalRows.scaled_regular z R B m a d h
  have vN := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) m
  have iN := GaussianNameArithmetic.multiply_fast powerF gammaF x y xN yN
  have xB := GaussianNameBounds.all_samples_bounded powerF x xN
  have yB := GaussianNameBounds.all_samples_bounded gammaF y yN
  have vB := GaussianNameBounds.all_samples_bounded referenceF v vN
  have iB := GaussianNamedBoundedProductObservation.sample_bounds powerF gammaF x y W G xB yB
  have inner := GaussianNamedBoundedProductObservation.sample_error powerF gammaF p x y W G xN yN xB yB
  have outer := GaussianNamedBoundedProductObservation.sample_error innerF referenceF p i v (W*G) V iN vN iB vB
  have pure := GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
      (GaussianNameBounds.sample_bound powerF x p xN) (GaussianNameBounds.sample_bound gammaF y p yN))
  have paid := GaussianNameRingLaws.product_left_error _ _ _ _ _ V (W*G) (unit_positive p) inner
    (GaussianNameBounds.sample_bound referenceF v p vN) pure
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) outer paid

theorem right_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (rightRaw p z R B m a d) (ap2 rightF p (rightData z R B m d)) (rightBudget z R B m d) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (raw_right_error p z R B m a d h)
    (distance_symmetric _ _ _ _ (unit_positive p) (named_right_error p z R B m a d h))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationCofinalProducts
