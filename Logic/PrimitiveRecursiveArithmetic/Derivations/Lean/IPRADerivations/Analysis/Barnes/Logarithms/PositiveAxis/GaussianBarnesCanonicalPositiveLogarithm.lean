import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveHeadLogarithm
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalSingleExponential
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorial

/-!
# Logarithm of the original Barnes evaluator on positive rational charts

Add the weighted real logarithms of the kept bases to the original
prefactor, finite corrections, and cofinal logarithm tail. The
exponential of this regular logarithm name agrees with the original
canonical Barnes value at independent observation precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithm

open_ipra
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRootAlgebra (equal equal_of_values re_sub im_sub re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (eval_re_code eval_im_code)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalPositiveHeadLogarithm.nameF
local notation "hd" => GaussianBarnesCanonicalPositiveHeadLogarithm.data
local notation "A" => GaussianBarnesCanonicalSingleExponential.exponentF
local notation "ad" => GaussianBarnesCanonicalSingleExponential.exponentData
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "E" => GaussianRadiusExponentialName.nameF

def source (a b R : PTm n) : Fm PTm n :=
  le one a ⋏ GaussianBarnesCanonicalLogCofinal.source (center a b) R b

abbrev nameF : PR 2 := addF H A
def data (a b R : PTm n) : PTm n := addData (hd a b (initial R)) (ad (center a b) R b)
def expData (a b R : PTm n) : PTm n := exponentialInputData nameF (data a b R)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (a b R : PTm n) :
    (source a b R).subst σ = source (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ R) := by simp [source,one]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (a b R : PTm n) :
    Syn.subst σ (data a b R) = data (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ R) := by simp [data]

private theorem center_equal (a b : PTm n) : Γ ⊢[PRAAx]
    equal (GaussianBarnesCanonicalHyperfactorial.center a b) (center a b) := by
  apply equal_of_values <;>
    simp only [GaussianBarnesCanonicalHyperfactorial.center,center,re_sub,im_sub,re_scale,im_scale,
      re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring

theorem default_source (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] source a b (a+b) := by
  have old := (GaussianBarnesCanonicalHyperfactorial.barnes_source a b hb).andE₂
  exact .andI ha (.andI hb (le_congr (GaussianRootAlgebra.normSq_equal (center_equal a b)) (.eqRefl _) old))

theorem regular (a b R : PTm n) (hs : Γ ⊢[PRAAx] source a b R) :
    Γ ⊢[PRAAx] pointCN nameF (data a b R) :=
  add_fast H A _ _ (GaussianBarnesCanonicalPositiveHeadLogarithm.regular a b _ hs.andE₁ hs.andE₂.andE₁)
    (GaussianBarnesCanonicalSingleExponential.exponent_regular _ _ _ hs.andE₂)

theorem exponential_value (a b R : PTm n) (hs : Γ ⊢[PRAAx] source a b R) : Γ ⊢[PRAAx]
    crossEquivalent (E nameF) V (expData a b R) (vd (center a b) R b) := by
  let z := center a b
  let N := initial R
  let x := hd a b N
  let y := ad z R b
  let h := exponentialInputData H x
  let c := exponentialInputData A y
  let q := GaussianBarnesCanonicalBaseProductShift.powerProduct z b N
  have hr := GaussianBarnesCanonicalPositiveHeadLogarithm.regular a b N hs.andE₁ hs.andE₂.andE₁
  have cr := GaussianBarnesCanonicalSingleExponential.exponent_regular z R b hs.andE₂
  have hi := exponential_input H x hr
  have ci := exponential_input A y cr
  have s := regular a b R hs
  have split := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent H A nameF
    (U H x) (U A y) (U nameF (data a b R)) x y (data a b R)
    hi ci (exponential_input _ _ s) (cross_refl _ _ s)
  have eh := GaussianRadiusExponentialName.name_regular H _ _ hi
  have ec := GaussianRadiusExponentialName.name_regular A _ _ ci
  have combine := GaussianGammaAdjacentCutoff.multiply_cross (E H) constantF (E A) (E A)
    h q c c eh (constant_regular q) ec ec
    (GaussianBarnesCanonicalPositiveHeadLogarithm.exponential_kept_powers a b N hs.andE₁ hs.andE₂.andE₁)
    (cross_refl _ _ ec)
  have value := GaussianBarnesCanonicalSingleExponential.factorization z R b hs.andE₂
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ combine (cross_symm _ _ _ _ value))

theorem actual_Barnes_positive_logarithm_exponentiates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let a := var 0
     let b := var 1
     let R := var 2
     source a b R ⟶ pointCN nameF (data a b R) ⋏ crossEquivalent (E nameF) V (expData a b R) (vd (center a b) R b)) :=
  closeUniv 3 (.impI (.andI (regular _ _ _ Prf.hyp0) (exponential_value _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithm
