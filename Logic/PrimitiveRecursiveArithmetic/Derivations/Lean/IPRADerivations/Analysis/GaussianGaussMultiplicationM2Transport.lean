import IPRADerivations.Analysis.GaussianGaussMultiplicationFixedFactors
import IPRADerivations.Analysis.GaussianGaussMultiplicationFixedProducts
import IPRADerivations.Analysis.GaussianGaussMultiplicationLimit

/-!
# From the fixed-cutoff M2 identity to the original Gauss limit

The finite hypothesis is a name identity at each selected cutoff.
Uniform bounds (independent of the cutoff) align its normalized
observations with the actual cofinal products.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationM2Transport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerReciprocalInverse (eulerF)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussMultiplicationCofinalRows (cutoff)
open GaussianGaussMultiplicationCofinalProducts (leftF leftData rightF rightData leftRaw rightRaw)
open GaussianGaussMultiplicationFixedFactors (scaledEulerData unitEulerData scaledBound unitBound powerBound)
open GaussianGaussMultiplicationFixedProducts (shiftedF shiftedData referenceF referenceData normalized_bounds normalized_error)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProduct (radius amplification)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRootApproximationWitness (pointBounds)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev fixedLeftF : PR 2 := multiplyF shiftedF eulerF
abbrev fixedInnerF : PR 2 := multiplyF powerF eulerF
abbrev fixedRightF : PR 2 := multiplyF fixedInnerF referenceF
def fixedLeftData (z R B m d N : PTm n) : PTm n :=
  multiplyData shiftedF eulerF (shiftedData z R B m d N) (unitEulerData m N)
def fixedInnerData (z R B m d N : PTm n) : PTm n :=
  multiplyData powerF eulerF (rowData z R B m N) (scaledEulerData z R B m d N)
def fixedRightData (z R B m d N : PTm n) : PTm n :=
  multiplyData fixedInnerF referenceF (fixedInnerData z R B m d N) (referenceData m N)

def m2At (N z R B m d : PTm n) : Fm PTm n :=
  crossEquivalent fixedLeftF fixedRightF (fixedLeftData z R B m d N) (fixedRightData z R B m d N)

def cofinalM2 (z R B m a d : PTm n) : Fm PTm n := .all
  (m2At (cutoff (var 0) (Syn.shift R) (Syn.shift m) (Syn.shift a) (Syn.shift d))
    (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift m) (Syn.shift d))

@[simp] theorem subst_m2At {l : ℕ} (σ : Fin n → PTm l) (N z R B m d : PTm n) :
    (m2At N z R B m d).subst σ =
      m2At (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) :=
  by simp [m2At,fixedLeftData,fixedRightData,fixedInnerData]
@[simp] theorem subst_cofinalM2 {l : ℕ} (σ : Fin n → PTm l) (z R B m a d : PTm n) :
    (cofinalM2 z R B m a d).subst σ =
      cofinalM2 (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) :=
  by simp [cofinalM2,Syn.subst_shift,Syn.shift_subst]

theorem cofinal_at (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] cofinalM2 z R B m a d) :
    Γ ⊢[PRAAx] m2At (cutoff p R m a d) z R B m d := by
  simpa only [cofinalM2,subst_m2At,GaussianGaussMultiplicationCofinalRows.subst_cutoff,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

def alignmentCost (A B V E F : PTm n) : PTm n := (E*V+A*F)+two*(A+B)

private theorem align_product (f g : PR 2) (p x y u v A B V E F : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hb : Γ ⊢[PRAAx] pointBounds f A x) (hc : Γ ⊢[PRAAx] pointBounds g B y)
    (hu : Γ ⊢[PRAAx] distanceBounded u (ap2 f p x) E (unit p))
    (hv : Γ ⊢[PRAAx] distanceBounded v (ap2 g p y) F (unit p))
    (hr : Γ ⊢[PRAAx] bounded v V one) : Γ ⊢[PRAAx]
    distanceBounded (qmul u v) (ap2 (multiplyF f g) p (multiplyData f g x y)) (alignmentCost A B V E F) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (GaussianNameArithmetic.product_distance _ _ _ _ E F (unit p) V A (unit_positive p) hu hv hr
      (GaussianRadiusExponentialName.bounded_samples_at f A x p hb))
    (distance_symmetric _ _ _ _ (unit_positive p)
      (GaussianNamedBoundedProductObservation.sample_error f g p x y A B hf hg hb hc))

private def shiftCap (R m d : PTm n) : PTm n := radius (GaussianGammaGaussEulerProduct.rowRadius R m d) m
private def refCap (m : PTm n) : PTm n := radius (GaussianGammaGaussReferenceEulerProduct.rowRadius m) m
private def shiftError (R m d : PTm n) : PTm n := two*amplification (GaussianGammaGaussEulerProduct.rowRadius R m d) m
private def refError (m : PTm n) : PTm n := two*amplification (GaussianGammaGaussReferenceEulerProduct.rowRadius m) m
private def fixedLeftBudget (R m d : PTm n) : PTm n := alignmentCost (shiftCap R m d) unitBound unitBound (shiftError R m d) two
private def fixedInnerBudget (z R B m d : PTm n) : PTm n :=
  alignmentCost (powerBound R m) (scaledBound z R B m d) (scaledBound z R B m d) zero two
private def fixedRightBudget (z R B m d : PTm n) : PTm n :=
  alignmentCost (powerBound R m*scaledBound z R B m d) (refCap m) (refCap m) (fixedInnerBudget z R B m d) (refError m)
def m2Budget (z R B m d : PTm n) : PTm n := (fixedLeftBudget R m d+two)+fixedRightBudget z R B m d

@[simp] theorem subst_m2Budget {l : ℕ} (σ : Fin n → PTm l) (z R B m d : PTm n) :
    Syn.subst σ (m2Budget z R B m d) = m2Budget (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [m2Budget,fixedLeftBudget,fixedRightBudget,fixedInnerBudget,alignmentCost,shiftCap,shiftError,refCap,refError,two]

theorem fixed_left_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) : Γ ⊢[PRAAx]
    distanceBounded (leftRaw p z R B m a d) (ap2 fixedLeftF p (fixedLeftData z R B m d (cutoff p R m a d)))
      (fixedLeftBudget R m d) (unit p) := by
  let N := cutoff p R m a d
  let L := GaussianGaussMultiplicationCofinalRows.scaledCutoff p R m a d
  let x := shiftedData z R B m d N
  let y := unitEulerData m N
  have hm := h.andE₁.andE₁
  have sh := GaussianGaussMultiplicationCofinalRows.shifted_cutoff p R m a d hm
  have un := GaussianGaussMultiplicationCofinalRows.unit_cutoff p R m a d hm
  have hu := GaussianGammaNormalization.unit_gamma_source (Γ := Γ)
  have bx := GaussianGaussMultiplicationFixedProducts.shifted_row_bounds p z R B m a d N h sh
  have rx := GaussianGaussMultiplicationFixedProducts.shifted_row_regular p z R B m a d N h sh
  have cx : Γ ⊢[PRAAx] pointCN shiftedF x := GaussianGaussMultiplicationFixedProducts.shifted_regular p z R B m a d N h sh
  have cy : Γ ⊢[PRAAx] pointCN eulerF y := GaussianGaussEulerCutoffUniform.euler_regular p oneCode one one one one L hu un
  have bx' : Γ ⊢[PRAAx] pointBounds shiftedF (shiftCap R m d) x := normalized_bounds _ _ _ _ _ bx
  have by' : Γ ⊢[PRAAx] pointBounds eulerF unitBound y :=
    GaussianGaussMultiplicationFixedFactors.euler_bounds p oneCode one one one one L hu un
  have dx := normalized_error _ p m _ _ bx rx
  have dy := GaussianNamedBoundedProductObservation.later_sample_error eulerF p (succ p) y cy (le_succ_self p)
  exact align_product shiftedF eulerF p x y _ _ _ _ _ _ _ cx cy bx' by' dx dy
    (GaussianRadiusExponentialName.bounded_samples_at eulerF unitBound y (succ p) by')

theorem fixed_right_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) : Γ ⊢[PRAAx]
    distanceBounded (rightRaw p z R B m a d) (ap2 fixedRightF p (fixedRightData z R B m d (cutoff p R m a d)))
      (fixedRightBudget z R B m d) (unit p) := by
  let N := cutoff p R m a d
  let L := GaussianGaussMultiplicationCofinalRows.scaledCutoff p R m a d
  let x := rowData z R B m N
  let y := scaledEulerData z R B m d N
  let v := referenceData m N
  let W := powerBound R m
  let G := scaledBound z R B m d
  let V := refCap m
  let i := fixedInnerData z R B m d N
  have hm := h.andE₁.andE₁
  have hn := GaussianGaussMultiplicationCofinalRows.cutoff_positive p R m a d hm
  have hs := GaussianGaussMultiplicationCofinalRows.scaled_cutoff p R m a d hm
  have hr := GaussianGaussMultiplicationCofinalRows.reference_cutoff p R m a d hm
  have cx := GaussianGaussMultiplicationFixedFactors.power_regular z R B m a d N h hn
  have bx := GaussianGaussMultiplicationFixedFactors.power_bounds z R B m a d N h hn
  have cy : Γ ⊢[PRAAx] pointCN eulerF y :=
    GaussianGaussEulerCutoffUniform.euler_regular p (scale m z) (scaledRadius R m) B a d L h.andE₂ hs
  have by' : Γ ⊢[PRAAx] pointBounds eulerF G y :=
    GaussianGaussMultiplicationFixedFactors.euler_bounds p (scale m z) (scaledRadius R m) B a d L h.andE₂ hs
  have cr := GaussianGaussMultiplicationFixedProducts.reference_regular p m N hr
  have rb := GaussianGaussMultiplicationFixedProducts.reference_row_bounds p m N hr
  have rr := GaussianGaussMultiplicationFixedProducts.reference_row_regular p m N hr
  have br : Γ ⊢[PRAAx] pointBounds referenceF V v := normalized_bounds _ _ _ _ _ rb
  have ci := GaussianNameArithmetic.multiply_fast powerF eulerF x y cx cy
  have bi : Γ ⊢[PRAAx] pointBounds fixedInnerF (W*G) i :=
    GaussianNamedBoundedProductObservation.sample_bounds powerF eulerF x y W G bx by'
  have dy := GaussianNamedBoundedProductObservation.later_sample_error eulerF p (succ p) y cy (le_succ_self p)
  have inner := align_product powerF eulerF p x y _ _ W G G zero two cx cy bx by'
    (GaussianRationalPowerDifference.distance_refl_zero (ap2 powerF p x) (unit p) (unit_positive p)) dy
    (GaussianRadiusExponentialName.bounded_samples_at eulerF G y (succ p) by')
  have dr := normalized_error _ p m _ _ rb rr
  have rawBound := GaussianGammaGaussReferenceEulerProduct.sample_bound p m N hr
  exact align_product fixedInnerF referenceF p i v _ _ (W*G) V V _ _ ci cr bi br inner dr rawBound

theorem m2_error (p z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] m2At (cutoff p R m a d) z R B m d) : Γ ⊢[PRAAx]
    distanceBounded (leftRaw p z R B m a d) (rightRaw p z R B m a d) (m2Budget z R B m d) (unit p) := by
  let N := cutoff p R m a d
  have U := unit_positive (Γ := Γ) p
  have main := GaussianNameEquivalence.cross_at fixedLeftF fixedRightF (fixedLeftData z R B m d N) (fixedRightData z R B m d N) p p hm
  have paid := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ U U) U
    (le_of_eq_add (d := zero) (by ipra_ring)) main
  exact distance_triangle_same _ _ _ _ _ _ U
    (distance_triangle_same _ _ _ _ _ _ U (fixed_left_error p z R B m a d hs) paid)
    (distance_symmetric _ _ _ _ U (fixed_right_error p z R B m a d hs))

theorem finite_agreement_from_m2 (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] cofinalM2 z R B m a d) : Γ ⊢[PRAAx]
    GaussianGaussMultiplicationLimit.finiteAgreement z R B m a d (m2Budget z R B m d) := by
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] cofinalM2 (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Fm.shift,Syn.shift,sh] using hm.shift
  simpa [GaussianGaussMultiplicationLimit.finiteAgreement,Syn.shift,sh] using
    m2_error (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) hs'
      (cofinal_at (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) hm')

theorem cleared_from_m2 (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] cofinalM2 z R B m a d) : Γ ⊢[PRAAx]
    crossEquivalent leftF rightF (leftData z R B m d) (rightData z R B m d) :=
  GaussianGaussMultiplicationLimit.cleared_from_finite_agreement _ _ _ _ _ _ _ hs (finite_agreement_from_m2 _ _ _ _ _ _ hs hm)

theorem actual_cleared_Gauss_from_named_M2_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ cofinalM2 (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      ⟶ crossEquivalent leftF rightF (leftData (var 0) (var 1) (var 2) (var 3) (var 5))
        (rightData (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (cleared_from_m2 _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationM2Transport
