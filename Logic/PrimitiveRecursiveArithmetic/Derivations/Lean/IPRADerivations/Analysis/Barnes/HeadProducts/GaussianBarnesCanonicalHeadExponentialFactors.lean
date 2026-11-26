import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHead
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalBaseProductShift
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalCorrectionShift
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteConstantFolds
import IPRADerivations.Analysis.Exponential.GaussianNamedFiniteExponentialFold
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamilyAlgebra

/-!
# Grouping the exponential corrections of the original Barnes head

Separate the actual head into its exact finite product of base powers
and the exponential of its exact finite correction sum. The proof
retains the original head name and applies even to vanishing factors.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadExponentialFactors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalHead (source parameters)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedFiniteProductFamily (rowF regularRows productData family_product_regular)
open GaussianNamedFiniteProductFamilyAlgebra (multiplyBody)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "headData" => GaussianBarnesCanonicalHead.headData
local notation "FP" => GaussianNamedFiniteProductName.nameF
local notation "C" => constantF
local notation "c" => GaussianBarnesCanonicalCorrectionShift.body
local notation "pointData" => GaussianBarnesCanonicalCorrectionShift.parameters
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "E" => Exp C
local notation "eBody" => GaussianNamedFiniteExponentialFold.exponentialBody C c

def exponentData (z B N : PTm n) : PTm n := exponentialInputData C (total z B N)
def nameF : PR 2 := multiplyF C E
def data (z B N : PTm n) : PTm n := multiplyData C E (powerProduct z B N) (exponentData z B N)

theorem regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data z B N) :=
  multiply_fast C E _ _ (constant_regular _) (GaussianRadiusExponentialName.name_regular C _ _
    (exponential_input C _ (constant_regular _)))

private theorem row_cross (z R B i : PTm n) (hs : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent F nameF (inst2 GaussianBarnesCanonicalHead.body i (parameters z R B zero))
      (inst2 (multiplyBody C E powerBody eBody) i (pointData z B)) := by
  let k := succ i
  let A := GaussianBarnesCanonicalFactor.exponentRadius R
  let b := GaussianBarnesCanonicalFactor.correction z B k
  let a := GaussianBarnesCanonicalFactor.powerValue z B k
  let X := GaussianBarnesCanonicalFactor.data z R B k
  let Y := multiplyData C E a (exponentialInputData C b)
  have ix : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source z R B k := .andI hs.andE₁ (.andI (zero_lt_succ i) hs.andE₂)
  have original := GaussianBarnesCanonicalFactor.exponential_input z R B k ix
  have folded := exponential_input C b (constant_regular (Γ := Γ) b)
  have exp := GaussianExponentialRadiusIndependence.same_input_cross C A (U C b) b original folded
  have reg := constant_regular (Γ := Γ) a
  have e : Γ ⊢[PRAAx] crossEquivalent F nameF X Y :=
    GaussianGammaAdjacentCutoff.multiply_cross C C E E a a _ _ reg reg
      (GaussianRadiusExponentialName.name_regular C A b original)
      (GaussianRadiusExponentialName.name_regular C (U C b) b folded) (cross_refl C a reg) exp
  have l : Γ ⊢[PRAAx] inst2 GaussianBarnesCanonicalHead.body i (parameters z R B zero) ≐ X := by
    refine (GaussianBarnesCanonicalHead.body_at i z R B zero).eqTrans ?_
    ipra_congr (GaussianBarnesCanonicalFactor.data (var 0) (var 1) (var 2) (var 3) : PTm 4) with
      [.eqRefl z, .eqRefl R, .eqRefl B, congrSucc (zero_add i)] using [X,k]
  have r : Γ ⊢[PRAAx] inst2 (multiplyBody C E powerBody eBody) i (pointData z B) ≐ Y := by
    rw [GaussianNamedFiniteProductFamilyAlgebra.body_at,GaussianNamedFiniteExponentialFold.exponentialBody_at]
    ipra_congr (multiplyData C E (var 0) (exponentialInputData C (var 1)) : PTm 2) with
      [GaussianBarnesCanonicalBaseProductShift.power_at i z B, GaussianBarnesCanonicalCorrectionShift.body_at i z B]
      using [Y,a,b,k,exponentialInputData,GaussianBarnesCanonicalPolynomialShift.data,
        GaussianBarnesCanonicalCorrectionShift.parameters]
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr F nameF _ _ _ _ l.eqSymm r.eqSymm e

theorem head_cross (z R B N : PTm n) (hs : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent H nameF (headData z R B N) (data z B N) := by
  let t := multiplyBody C E powerBody eBody
  let X := parameters z R B zero
  let Y := pointData z B
  let l := productData C powerBody N Y
  let r := productData E eBody N Y
  let A := FP (rowF C powerBody)
  let B' := FP (rowF E eBody)
  let S := GaussianNamedFiniteSumFamily.nameF C c
  let u := total z B N
  let d := GaussianNamedFiniteSumFamily.data N Y
  have cp := GaussianNamedFiniteConstantFolds.rows_regular (Γ := Γ) powerBody N Y
  have cc := GaussianNamedFiniteConstantFolds.rows_regular (Γ := Γ) c N Y
  have ce := GaussianNamedFiniteExponentialFold.exponential_rows C c N Y cc
  have cf := GaussianNamedFiniteProductFamilyAlgebra.multiply_regular C E powerBody eBody N Y cp ce
  have equality : Γ ⊢[PRAAx] equalRows F nameF GaussianBarnesCanonicalHead.body t N X Y := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let sh (x : PTm n) := Syn.shift x
    have h : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hs.shift.wk
    simpa only [Syn.shift,GaussianBarnesCanonicalHead.subst_parameters,GaussianBarnesCanonicalCorrectionShift.subst_parameters,
      ConciseIPRA.PTm.subst_zero,Δ,sh,X,Y,t] using row_cross (sh z) (sh R) (sh B) (var 0) h
  have rearrange := family_product_cross F nameF GaussianBarnesCanonicalHead.body t N X Y
    (GaussianBarnesCanonicalHead.rows_regular z R B zero N hs) cf equality
  have distribute := GaussianNamedFiniteProductFamilyAlgebra.family_multiply_cross C E powerBody eBody N Y cp ce
  have powers := GaussianNamedFiniteConstantFolds.product_cross (Γ := Γ) powerBody N Y
  have sums := GaussianNamedFiniteConstantFolds.sum_cross (Γ := Γ) c N Y
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper S C (U S d) (U C u) d u
    (exponential_input S d (GaussianNamedFiniteSumFamily.regular C c N Y cc))
    (exponential_input C u (constant_regular u)) sums
  have fold := GaussianNameEquivalence.cross_symm _ _ _ _
    (GaussianNamedFiniteExponentialFold.exponential_product_cross C c N Y cc)
  have exponent := cross_trans B' (Exp S) E r (exponentialInputData S d) (exponentData z B N) fold exp
  have collect := GaussianGammaAdjacentCutoff.multiply_cross A C B' E l (powerProduct z B N) r (exponentData z B N)
    (family_product_regular C powerBody N Y cp) (constant_regular _)
    (family_product_regular E eBody N Y ce)
    (GaussianRadiusExponentialName.name_regular C _ _ (exponential_input C _ (constant_regular _))) powers exponent
  exact cross_trans _ _ _ _ _ _ rearrange (cross_trans _ _ _ _ _ _ distribute collect)

theorem actual_Barnes_original_head_exponential_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent H nameF
      (headData (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (head_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadExponentialFactors
