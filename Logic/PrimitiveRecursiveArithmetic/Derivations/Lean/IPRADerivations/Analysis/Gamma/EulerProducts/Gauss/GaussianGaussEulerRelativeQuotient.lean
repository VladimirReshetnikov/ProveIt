import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerFiniteIdentity
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerFiniteApartness
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionQuotient

/-!
# Gauss's exact finite quotient of quotients

Evaluate the two inner quotients by the actual reciprocal of the
appropriate finite Euler Gamma name. The positive reference rows
give a reciprocal clock for the normalized reference quotient.
Cancellation recovers (M2) from the cleared identity at the same
finite cutoff, with no additional apartness hypotheses.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerRelativeQuotient

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianBoundedInverseApartness (bounded_inverse_input height ones_equivalent)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerReciprocalInverse (eulerF)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaGaussEulerHeads (cutoff)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (inverse_pairs named_product_exchange)
open GaussianGaussEulerFiniteApartness (inverseApartClock euler_apart referenceApartClock reference_input)
open GaussianGaussEulerFiniteIdentity (finiteCutoffs finite_identity)
open GaussianGaussMultiplicationFixedFactors (scaledEulerData unitEulerData power_regular)
open GaussianGaussMultiplicationFixedProducts (shiftedF shiftedData shifted_regular referenceF referenceData)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U U_positive sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameReciprocal (apart input nameF nameData name_fast product_one product_one_left)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative multiply_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "needed" => GaussianGammaEulerInverseApproximationName.cutoff

abbrev inverseEulerF : PR 2 := nameF eulerF
def unitInverseData (m N : PTm n) : PTm n :=
  nameData (inverseApartClock qF (qData oneCode one (cutoff m N))) (unitEulerData m N)
def scaledInverseData (z R B m d N : PTm n) : PTm n :=
  nameData (inverseApartClock qF (qData (scale m z) B (cutoff m N))) (scaledEulerData z R B m d N)
def refInverseData (m N : PTm n) : PTm n :=
  nameData (referenceApartClock m N) (referenceData m N)

abbrev argumentUF : PR 2 := multiplyF shiftedF inverseEulerF
abbrev referenceUF : PR 2 := multiplyF referenceF inverseEulerF
def argumentUData (z R B m d N : PTm n) : PTm n :=
  multiplyData shiftedF inverseEulerF (shiftedData z R B m d N) (scaledInverseData z R B m d N)
def referenceUData (m N : PTm n) : PTm n :=
  multiplyData referenceF inverseEulerF (referenceData m N) (unitInverseData m N)

abbrev referenceInverseCandidateF : PR 2 := multiplyF (nameF referenceF) eulerF
def referenceInverseCandidateData (m N : PTm n) : PTm n :=
  multiplyData (nameF referenceF) eulerF (refInverseData m N) (unitEulerData m N)

def relativeHeight (m N : PTm n) : PTm n :=
  let x := referenceInverseCandidateData m N
  height referenceUF referenceInverseCandidateF (referenceUData m N) x (U referenceInverseCandidateF x)

abbrev quotientF : PR 2 := multiplyF argumentUF (nameF referenceUF)
def quotientData (z R B m d N : PTm n) : PTm n :=
  multiplyData argumentUF (nameF referenceUF) (argumentUData z R B m d N)
    (nameData (relativeHeight m N) (referenceUData m N))

private theorem bounded_samples (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] smallSamples f x (U f x) one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using h.shift
  simpa only [smallSamples,Syn.shift,GaussianNameBounds.subst_U,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using sample_bound f (Syn.shift x) (var 0) hs

private theorem unit_source (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (needed s one one one) (cutoff m N)) :
    Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source oneCode one one one one (cutoff m N) := by
  have h := GaussianGammaNormalization.unit_gamma_source (Γ := Γ) (n := n)
  exact .andI h (GaussianGaussEulerCutoffUniform.cutoff_source s oneCode one one one one _ h hn).andE₂.andE₁

theorem reference_quotient_input (s m N : PTm n)
    (hn : Γ ⊢[PRAAx] le (GaussianGammaGaussReferenceEulerProduct.threshold s m) N)
    (hu : Γ ⊢[PRAAx] le (needed s one one one) (cutoff m N)) :
    Γ ⊢[PRAAx] input referenceUF (relativeHeight m N) (referenceUData m N) := by
  let x := referenceData m N
  let y := unitEulerData m N
  let u := refInverseData m N
  let v := unitInverseData m N
  let c := referenceApartClock m N
  let b := inverseApartClock qF (qData oneCode one (cutoff m N))
  let X := referenceUData m N
  let Y := referenceInverseCandidateData m N
  have src := unit_source s m N hu
  have hx := (reference_input s m N hn).andE₁
  have ax := (reference_input s m N hn).andE₂
  have hy : Γ ⊢[PRAAx] pointCN eulerF y := GaussianGammaEulerReciprocalInverse.euler_regular _ _ _ _ _ _ src
  have ay : Γ ⊢[PRAAx] apart eulerF b y := euler_apart _ _ _ _ _ _ src
  have hx' : Γ ⊢[PRAAx] pointCN (nameF referenceF) u := name_fast referenceF c x hx ax
  have hy' : Γ ⊢[PRAAx] pointCN inverseEulerF v := name_fast eulerF b y hy ay
  have fx : Γ ⊢[PRAAx] pointCN referenceUF X := multiply_fast referenceF inverseEulerF x v hx hy'
  have fy : Γ ⊢[PRAAx] pointCN referenceInverseCandidateF Y := multiply_fast _ _ _ _ hx' hy
  have cx := cross_trans _ _ _ _ _ _ (product_one referenceF c x hx ax) (ones_equivalent x X)
  have cy := cross_trans _ _ _ _ _ _ (product_one_left eulerF b y hy ay) (ones_equivalent y X)
  have e := inverse_pairs referenceF inverseEulerF (nameF referenceF) eulerF x v u y X hx hy' hx' hy cx cy
  exact bounded_inverse_input referenceUF referenceInverseCandidateF X Y (U referenceInverseCandidateF Y) one
    (U_positive _ _) (le_refl one) fx fy (bounded_samples _ _ fy) e

private theorem cancel_product (F G I : PR 2) (x y v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hi : Γ ⊢[PRAAx] pointCN I v)
    (e : Γ ⊢[PRAAx] crossEquivalent (multiplyF G I) oneF (multiplyData G I y v) y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF F (multiplyF G I)) F
      (multiplyData F (multiplyF G I) x (multiplyData G I y v)) x := by
  have unit := cross_trans _ _ _ _ _ _ e (ones_equivalent y x)
  have gone := multiply_cross F F (multiplyF G I) oneF x x (multiplyData G I y v) x hf hf
    (multiply_fast G I y v hg hi) (one_fast x) (cross_refl _ _ hf) unit
  exact cross_trans _ _ _ _ _ _ gone (multiply_one F x hf)

theorem relative_quotient (s z R B m a d N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B m a d) (hn : Γ ⊢[PRAAx] finiteCutoffs s R m a d N) :
    Γ ⊢[PRAAx] crossEquivalent quotientF powerF (quotientData z R B m d N) (rowData z R B m N) := by
  let L := cutoff m N
  let J := inverseEulerF
  let x := shiftedData z R B m d N
  let y := unitEulerData m N
  let u := scaledEulerData z R B m d N
  let v := referenceData m N
  let w := rowData z R B m N
  let iy := unitInverseData m N
  let iu := scaledInverseData z R B m d N
  let t := multiplyData J J iu iy
  let Au := argumentUData z R B m d N
  let Ru := referenceUData m N
  let P := multiplyF powerF eulerF
  let px := multiplyData powerF eulerF w u
  have nS := hn.andE₂.andE₁
  have nR := hn.andE₂.andE₂.andE₁
  have nU := hn.andE₂.andE₂.andE₂.andE₁
  have nZ := hn.andE₂.andE₂.andE₂.andE₂
  have hs := h.andE₂
  have uy := unit_source s m N nU
  have uz : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source (scale m z) (scaledRadius R m) B a d L :=
    .andI hs (GaussianGaussEulerCutoffUniform.cutoff_source s (scale m z) (scaledRadius R m) B a d L hs nZ).andE₂.andE₁
  have hx := shifted_regular s z R B m a d N h nS
  have hv := (reference_input s m N nR).andE₁
  have hw := power_regular z R B m a d N h hn.andE₁
  have hy : Γ ⊢[PRAAx] pointCN eulerF y := GaussianGammaEulerReciprocalInverse.euler_regular _ _ _ _ _ _ uy
  have hu : Γ ⊢[PRAAx] pointCN eulerF u := GaussianGammaEulerReciprocalInverse.euler_regular _ _ _ _ _ _ uz
  have dy : Γ ⊢[PRAAx] apart eulerF (inverseApartClock qF (qData oneCode one L)) y := euler_apart _ _ _ _ _ _ uy
  have du : Γ ⊢[PRAAx] apart eulerF (inverseApartClock qF (qData (scale m z) B L)) u := euler_apart _ _ _ _ _ _ uz
  have hiy : Γ ⊢[PRAAx] pointCN J iy := name_fast _ _ _ hy dy
  have hiu : Γ ⊢[PRAAx] pointCN J iu := name_fast _ _ _ hu du
  have hAu : Γ ⊢[PRAAx] pointCN argumentUF Au := multiply_fast shiftedF J x iu hx hiu
  have hRu : Γ ⊢[PRAAx] pointCN referenceUF Ru := multiply_fast referenceF J v iy hv hiy
  have hp : Γ ⊢[PRAAx] pointCN P px := multiply_fast powerF eulerF w u hw hu
  have ht : Γ ⊢[PRAAx] pointCN (multiplyF J J) t := multiply_fast J J iu iy hiu hiy
  have finiteEq := finite_identity s z R B m a d N h hn
  have scaleBoth := multiply_cross (multiplyF shiftedF eulerF) (multiplyF P referenceF)
    (multiplyF J J) (multiplyF J J) (multiplyData shiftedF eulerF x y)
    (multiplyData P referenceF px v) t t (multiply_fast _ _ _ _ hx hy) (multiply_fast _ _ _ _ hp hv)
    ht ht finiteEq (cross_refl _ _ ht)

  have leftExchange := named_product_exchange shiftedF eulerF J J x y iu iy hx hy hiu hiy
  have leftCancel := cancel_product argumentUF eulerF J Au y iy hAu hy hiy (product_one _ _ _ hy dy)
  have leftSimple := cross_trans _ _ _ _ _ _ leftExchange leftCancel

  have rightExchange := named_product_exchange P referenceF J J px v iu iy hp hv hiu hiy
  have pAssoc := multiply_associative powerF eulerF J w u iu hw hu hiu
  have pCancel := cancel_product powerF eulerF J w u iu hw hu hiu (product_one _ _ _ hu du)
  have pSimple := cross_trans _ _ _ _ _ _ pAssoc pCancel
  have rightCancel := multiply_cross (multiplyF P J) powerF referenceUF referenceUF
    (multiplyData P J px iu) w Ru Ru (multiply_fast _ _ _ _ hp hiu) hw hRu hRu pSimple (cross_refl _ _ hRu)
  have rightComm := multiply_commutative powerF referenceUF w Ru hw hRu
  have rightSimple := cross_trans _ _ _ _ _ _ rightExchange (cross_trans _ _ _ _ _ _ rightCancel rightComm)
  have uIdentity : Γ ⊢[PRAAx] crossEquivalent (multiplyF referenceUF powerF) argumentUF
      (multiplyData referenceUF powerF Ru w) Au :=
    cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ leftSimple)
      (cross_trans _ _ _ _ _ _ scaleBoth rightSimple))

  have hRecip := reference_quotient_input s m N nR nU
  exact cross_symm _ _ _ _ (GaussianGammaReflectionQuotient.divide_cleared referenceUF powerF argumentUF
    Ru w Au (relativeHeight m N) hRu hw hAu hRecip.andE₂ uIdentity)

theorem actual_finite_Gauss_relative_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏
      finiteCutoffs (var 0) (var 2) (var 4) (var 5) (var 6) (var 7)) ⟶
      crossEquivalent quotientF powerF (quotientData (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
        (rowData (var 1) (var 2) (var 3) (var 4) (var 7))) :=
  closeUniv 8 (.impI (relative_quotient _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerRelativeQuotient
