import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.GaussianGaussMultiplicationCofinalProducts
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferencePrefix
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment

/-!
# Gauss multiplication in its divided form

The original reciprocal Gamma name at the scaled argument supplies a
uniform bound for the inverse of the original Gamma name. This gives
a clock for reciprocal evaluation on the actual denominator in (M4).
Multiplying the cleared identity by that reciprocal and removing the
terminal unit row leaves the normalized prefix in the paper.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationQuotient

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianBoundedInverseApartness (bounded_inverse_correct height ones_equivalent)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF gamma_product named_product_exchange)
open GaussianGaussMultiplicationCofinalProducts
  (leftF leftData left_regular rightF rightData right_regular innerF innerData referenceF referenceData)
open GaussianGaussMultiplicationCofinalRows (scaledData scaled_regular limit_power_regular)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U U_positive sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative multiply_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "reciprocalGammaF" => GaussianGammaC7Name.nameF
local notation "reciprocalGammaData" => GaussianGammaC7Name.data

def scaledReciprocalHeight (z R B m d : PTm n) : PTm n :=
  let w := reciprocalGammaData (scale m z) (scaledRadius R m) B
  height gammaF reciprocalGammaF (scaledData z R B m d) w (U reciprocalGammaF w)

abbrev scaledReciprocalF : PR 2 := GaussianNameReciprocal.nameF gammaF
def scaledReciprocalData (z R B m d : PTm n) : PTm n :=
  GaussianNameReciprocal.nameData (scaledReciprocalHeight z R B m d) (scaledData z R B m d)

theorem scaled_reciprocal (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input gammaF (scaledReciprocalHeight z R B m d) (scaledData z R B m d) ⋏
      crossEquivalent scaledReciprocalF reciprocalGammaF (scaledReciprocalData z R B m d)
        (reciprocalGammaData (scale m z) (scaledRadius R m) B) := by
  let v := scale m z
  let S := scaledRadius R m
  let x := scaledData z R B m d
  let y := reciprocalGammaData v S B
  have gx := scaled_regular z R B m a d h
  have gy := GaussianGammaC7Name.name_regular v S B h.andE₂.andE₁
  have hb : Γ ⊢[PRAAx] smallSamples reciprocalGammaF y (U reciprocalGammaF y) one := by
    refine .allI ?_
    have ys : Γ.map Fm.shift ⊢[PRAAx] pointCN reciprocalGammaF (Syn.shift y) := by
      simpa only [Fm.shift,subst_pointCN,Syn.shift] using gy.shift
    simpa only [smallSamples,Syn.shift,GaussianNameBounds.subst_U,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      sample_bound reciprocalGammaF (Syn.shift y) (var 0) ys
  have comm := multiply_commutative gammaF reciprocalGammaF x y gx gy
  have prod : Γ ⊢[PRAAx] crossEquivalent (multiplyF reciprocalGammaF gammaF) oneF
      (multiplyData reciprocalGammaF gammaF y x) y := gamma_product v S B a d h.andE₂
  have unit : Γ ⊢[PRAAx] crossEquivalent (multiplyF gammaF reciprocalGammaF) oneF
      (multiplyData gammaF reciprocalGammaF x y) x :=
    cross_trans _ _ _ _ _ _ comm (cross_trans _ _ _ _ _ _ prod (ones_equivalent y x))
  exact bounded_inverse_correct gammaF reciprocalGammaF x y (U reciprocalGammaF y) one
    (U_positive _ _) (le_refl one) gx gy hb unit

def prefixData (m : PTm n) : PTm n := GaussianGammaGaussReferencePrefix.data (pred m)

theorem reference_prefix (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent referenceF referenceF (referenceData m) (prefixData m) := by
  have e : Γ ⊢[PRAAx] m ≐ succ (pred m) := by
    refine .orE (zero_or_succ m) ?_ Prf.hyp0
    exact lt_zero_absurd _ (le_congr (.eqRefl _) Prf.hyp0 hm.wk)
  have hd : Γ ⊢[PRAAx] referenceData m ≐ referenceData (succ (pred m)) := by
    simpa only [referenceData,GaussianGammaGaussReferenceProduct.subst_data,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (referenceData (var 0) : PTm 1)
        (σ := ![m]) (σ' := ![succ (pred m)]) (fun i => by fin_cases i; exact e)
  exact cross_data_congr referenceF referenceF _ _ _ _ hd.eqSymm (.eqRefl _)
    (GaussianGammaGaussReferencePrefix.full_prefix_cross (pred m))

abbrev leftQuotientF : PR 2 := multiplyF leftF scaledReciprocalF
abbrev rightQuotientF : PR 2 := multiplyF powerF referenceF
def leftQuotientData (z R B m d : PTm n) : PTm n :=
  multiplyData leftF scaledReciprocalF (leftData z R B m d) (scaledReciprocalData z R B m d)
def rightQuotientData (z R B m : PTm n) : PTm n :=
  multiplyData powerF referenceF (limitData z R B m) (prefixData m)

theorem quotient_from_cleared (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hc : Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData z R B m d) (rightData z R B m d)) :
    Γ ⊢[PRAAx] crossEquivalent leftQuotientF rightQuotientF
      (leftQuotientData z R B m d) (rightQuotientData z R B m) := by
  let x := leftData z R B m d
  let y := rightData z R B m d
  let w := limitData z R B m
  let s := scaledData z R B m d
  let r := referenceData m
  let I := scaledReciprocalF
  let v := scaledReciprocalData z R B m d
  have hf := left_regular z R B m a d h
  have hg := right_regular z R B m a d h
  have hp := limit_power_regular z R B m a d h
  have hs := scaled_regular z R B m a d h
  have hr := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) m
  have hi := (scaled_reciprocal z R B m a d h).andE₁
  have hv : Γ ⊢[PRAAx] pointCN I v := GaussianNameReciprocal.name_fast _ _ _ hi.andE₁ hi.andE₂
  have first := multiply_cross leftF rightF I I x y v v hf hg hv hv hc (cross_refl _ _ hv)
  have assoc := multiply_associative innerF referenceF I (innerData z R B m d) r v
    (multiply_fast powerF gammaF w s hp hs) hr hv
  have exchange := named_product_exchange powerF gammaF referenceF I w s r v hp hs hr hv
  have cancel := GaussianNameReciprocal.product_one gammaF (scaledReciprocalHeight z R B m d) s hi.andE₁ hi.andE₂
  let D := multiplyData powerF referenceF w r
  have hD : Γ ⊢[PRAAx] pointCN rightQuotientF D := multiply_fast _ _ _ _ hp hr
  have unit := cross_trans _ _ _ _ _ _ cancel (ones_equivalent s D)
  have replace := multiply_cross rightQuotientF rightQuotientF (multiplyF gammaF I) oneF D D
    (multiplyData gammaF I s v) D hD hD (multiply_fast _ _ _ _ hs hv) (one_fast D)
    (cross_refl _ _ hD) unit
  have pref := multiply_cross powerF powerF referenceF referenceF w w r (prefixData m) hp hp hr
    (GaussianGammaGaussReferencePrefix.name_regular (pred m)) (cross_refl _ _ hp)
    (reference_prefix m h.andE₁.andE₁)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ exchange (cross_trans _ _ _ _ _ _ replace
      (cross_trans _ _ _ _ _ _ (multiply_one _ _ hD) pref))))

theorem actual_divided_Gauss_from_cleared_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent leftF rightF (leftData (var 0) (var 1) (var 2) (var 3) (var 5))
        (rightData (var 0) (var 1) (var 2) (var 3) (var 5)) ⟶
      crossEquivalent leftQuotientF rightQuotientF (leftQuotientData (var 0) (var 1) (var 2) (var 3) (var 5))
        (rightQuotientData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (.impI (quotient_from_cleared _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationQuotient
