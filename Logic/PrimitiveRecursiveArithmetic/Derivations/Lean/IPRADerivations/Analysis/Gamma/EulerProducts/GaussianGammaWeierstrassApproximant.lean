import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassFiniteName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.Gamma.GaussianGammaReciprocalInverse

/-!
# The literal C5 Weierstrass approximant

Attach the original Euler-constant exponential to the product whose
samples evaluate every individual negative exponential. Named ring
laws and the actual exponential-addition theorem identify this program
with the original folded `P_N`, including at zeros of the polynomial head.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassApproximant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent
  (source gammaF gamma_regular constantF constant_at constant_regular differenceF differenceData difference_regular
    harmonicPoint productF productData product_regular)
open GaussianGammaFiniteApproximantName (pF pData exponentialInputData exponential_input p_regular)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (add_commutative multiply_commutative multiply_associative distributive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (canonical ofGaussian qmul qzero)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianGammaWeierstrassFactors (width harmonicArgument)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveExponentF : PR 2 := multiplyF gammaF constantF
def positiveExponentData (z B : PTm n) : PTm n := multiplyData gammaF constantF zero (ofGaussian z B)
def positiveExpF : PR 2 := GaussianRadiusExponentialName.nameF positiveExponentF
def positiveExpData (z B : PTm n) : PTm n := exponentialInputData positiveExponentF (positiveExponentData z B)

def literalF : PR 2 := multiplyF GaussianGammaWeierstrassFiniteName.nameF positiveExpF
def literalData (z R B N : PTm n) : PTm n := multiplyData GaussianGammaWeierstrassFiniteName.nameF positiveExpF
  (GaussianGammaWeierstrassFiniteName.nameData z R B N) (positiveExpData z B)

theorem positive_exponent_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN positiveExponentF (positiveExponentData z B) :=
  multiply_fast _ _ _ _ gamma_regular (constant_regular _)

theorem positive_exp_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN positiveExpF (positiveExpData z B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (positive_exponent_regular z B))

theorem literal_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    pointCN literalF (literalData z R B N) :=
  multiply_fast _ _ _ _ (GaussianGammaWeierstrassFiniteName.name_regular z R B N h) (positive_exp_regular z B)

theorem constant_product_cross (x y : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF x y) (qmul x y) := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let a := Syn.shift (Syn.shift x)
  let b := Syn.shift (Syn.shift y)
  have e : C ⊢[PRAAx] ap2 (multiplyF constantF constantF) (var 1) (multiplyData constantF constantF a b) ≐ qmul a b :=
    (GaussianGammaReciprocalInverse.constant_product_sample _ _ _).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))
  have p := cross_at (Γ := C) _ _ _ _ (var 1) (var 0) (cross_refl constantF (qmul a b) (constant_regular _))
  have q := distance_congr ((constant_at (Γ := C) (var 1) (qmul a b)).eqTrans e.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) p
  simpa only [crossEquivalent,Syn.shift,GaussianNameArithmetic.subst_multiplyData,GaussianRationalHorner.subst_qmul,C,a,b] using q

theorem constant_data_cross (x y : PTm n) (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] crossEquivalent constantF constantF x y := by
  have r := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent constantF constantF (var 0) (var 1) : Fm PTm 2)
    ![x,x] ![x,y] (fun i => by fin_cases i; exact .eqRefl _; exact h)
    (by simpa using cross_refl constantF x (constant_regular x))
  simpa using r

theorem harmonic_product_cross (z B N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF (ofGaussian z B) (qnegative (harmonicPoint N))) (harmonicArgument z B N) := by
  let x := ofGaussian z B
  let a := harmonicPoint N
  have eq : Γ ⊢[PRAAx] qmul x (qnegative a) ≐ harmonicArgument z B N :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)).eqSymm (.eqRefl _))
  exact cross_trans _ _ _ _ _ _ (constant_product_cross x (qnegative a)) (constant_data_cross _ _ eq)

theorem exponent_sum_equivalent (z B N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (addF constantF positiveExponentF) productF
      (addData (harmonicArgument z B N) (positiveExponentData z B)) (productData z B N) := by
  let x := ofGaussian z B
  let h := qnegative (harmonicPoint N)
  let A := multiplyF constantF gammaF
  let a := multiplyData constantF gammaF x zero
  let C := multiplyF constantF constantF
  let c := multiplyData constantF constantF x h
  let t := harmonicArgument z B N
  have hx := constant_regular (Γ := Γ) x
  have hh := constant_regular (Γ := Γ) h
  have hg := gamma_regular (Γ := Γ) (n := n)
  have ha : Γ ⊢[PRAAx] pointCN A a := multiply_fast _ _ _ _ hx hg
  have hc : Γ ⊢[PRAAx] pointCN C c := multiply_fast _ _ _ _ hx hh
  have e := multiply_commutative differenceF constantF (differenceData N) x (difference_regular N) hx
  have dist := distributive constantF gammaF constantF x zero h hx hg hh
  have aγ := multiply_commutative constantF gammaF x zero hx hg
  have aH := harmonic_product_cross (Γ := Γ) z B N
  have swap := add_equivalent A positiveExponentF C constantF a (positiveExponentData z B) c t ha
    (positive_exponent_regular z B) hc (constant_regular t) (cross_to_diagonal _ _ _ _ aγ)
    (cross_to_diagonal _ _ _ _ aH)
  have pair := add_commutative (Γ := Γ) positiveExponentF constantF (positiveExponentData z B) t
    (positive_exponent_regular z B) (constant_regular t)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ e
    (cross_trans _ _ _ _ _ _ dist (cross_trans _ _ _ _ _ _ swap pair)))

theorem original_finite_identity (z R B N : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent literalF pF (literalData z R B N) (pData z B N) := by
  let H := GaussianGammaEulerHead.head z B N
  let J := GaussianGammaEulerHead.run z B N
  let X := GaussianGammaWeierstrassFiniteName.exponentData z R B N
  let Y := positiveExpData z B
  let W := GaussianGammaWeierstrassFiniteName.exponentF
  let Z := exponentialInputData productF (productData z B N)
  let T := GaussianRadiusExponentialName.nameF productF
  have hH := constant_regular (Γ := Γ) H
  have hJ := constant_regular (Γ := Γ) J
  have hX : Γ ⊢[PRAAx] pointCN W X := GaussianGammaWeierstrassFiniteName.exponent_regular z R B N hs
  have hY := positive_exp_regular (Γ := Γ) z B
  have hZ : Γ ⊢[PRAAx] pointCN T Z :=
    GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (product_regular z B N))
  have first := multiply_cross GaussianGammaWeierstrassFiniteName.nameF GaussianGammaWeierstrassFiniteName.foldedF
    positiveExpF positiveExpF (GaussianGammaWeierstrassFiniteName.nameData z R B N)
    (GaussianGammaWeierstrassFiniteName.foldedData z R B N) Y Y
    (GaussianGammaWeierstrassFiniteName.name_regular z R B N hs) (multiply_fast _ _ _ _ hH hX) hY hY
    (GaussianGammaWeierstrassFiniteName.name_equivalent z R B N hs) (cross_refl _ _ hY)
  have assoc := multiply_associative constantF W positiveExpF H X Y hH hX hY
  have ef : Γ ⊢[PRAAx] crossEquivalent (multiplyF W positiveExpF) T (multiplyData W positiveExpF X Y) Z :=
    GaussianGammaFoldedApproximantBalance.exponential_product_equivalent constantF positiveExponentF productF
      (width R N) _ _ (harmonicArgument z B N) (positiveExponentData z B) (productData z B N)
      (GaussianGammaWeierstrassFiniteName.exponent_input z R B N hs)
      (exponential_input _ _ (positive_exponent_regular z B)) (exponential_input _ _ (product_regular z B N))
      (exponent_sum_equivalent z B N)
  have rest := multiply_cross constantF constantF (multiplyF W positiveExpF) T H J (multiplyData W positiveExpF X Y) Z
    hH hJ (multiply_fast _ _ _ _ hX hY) hZ
    (constant_data_cross H J (GaussianGammaEulerHead.program_at z B N).eqSymm) ef
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc rest)

theorem original_literal_C5_program_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ pointCN literalF (literalData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (literal_regular _ _ _ _ Prf.hyp0))

theorem original_literal_C5_weierstrass_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent literalF pF
      (literalData (var 0) (var 1) (var 2) (var 3)) (pData (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_finite_identity _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassApproximant
