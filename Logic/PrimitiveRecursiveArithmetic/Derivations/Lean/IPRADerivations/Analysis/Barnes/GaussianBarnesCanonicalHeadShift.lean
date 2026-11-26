import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# Division-free shift of the original finite Barnes head

The shifted head times the plain Gamma polynomial equals the original
head times the endpoint power and the exponential of the harmonic
correction. Both sides use the actual head and exponential names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalBaseProductShift (powerProduct terminal power_shift)
open GaussianBarnesCanonicalCorrectionShift (exponent total total_shift)
open GaussianBarnesCanonicalHead (source headData)
open GaussianBarnesCanonicalPolynomialShift (plain)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "F" => GaussianBarnesCanonicalHeadExponentialFactors.nameF
local notation "FData" => GaussianBarnesCanonicalHeadExponentialFactors.data
local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF C
local notation "expData" => exponentialInputData C

def leftF : PR 2 := multiplyF H C
def leftData (z S B N : PTm n) : PTm n := multiplyData H C (headData (translated z B one) S B N) (plain z B N)
def rightF : PR 2 := multiplyF H F
def multiplierData (z B N : PTm n) : PTm n := multiplyData C E (terminal z B N) (expData (exponent z B N))
def rightData (z R B N : PTm n) : PTm n := multiplyData H F (headData z R B N) (multiplierData z B N)

private theorem exp_regular (a : PTm n) : Γ ⊢[PRAAx] pointCN E (expData a) :=
  GaussianRadiusExponentialName.name_regular C _ _ (exponential_input C a (constant_regular _))

private theorem collect_constants (G : PR 2) (a b x : PTm n) (h : Γ ⊢[PRAAx] pointCN G x) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF C G) C) (multiplyF C G)
      (multiplyData (multiplyF C G) C (multiplyData C G a x) b) (multiplyData C G (qmul a b) x) := by
  let ga := constant_regular (Γ := Γ) a
  let gb := constant_regular (Γ := Γ) b
  let comm := multiply_commutative G C x b h gb
  let swap := multiply_cross C C (multiplyF G C) (multiplyF C G) a a (multiplyData G C x b) (multiplyData C G b x)
    ga ga (multiply_fast _ _ _ _ h gb) (multiply_fast _ _ _ _ gb h) (cross_refl _ _ ga) comm
  let combine := multiply_cross (multiplyF C C) C G G (multiplyData C C a b) (qmul a b) x x
    (multiply_fast _ _ _ _ ga gb) (constant_regular _) h h (constant_product_cross a b) (cross_refl _ _ h)
  exact cross_trans _ _ _ _ _ _ (multiply_associative C G C a x b ga h gb)
    (cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _
      (multiply_associative C C G a b x ga gb h)) combine))

theorem exponential_shift (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF E E) E (multiplyData E E (expData (total z B N)) (expData (exponent z B N)))
      (expData (total (translated z B one) B N)) := by
  let a := total z B N
  let b := exponent z B N
  let w := total (translated z B one) B N
  have eq : Γ ⊢[PRAAx] qadd a b ≐ w :=
    (qadd_congr (.eqRefl _) (total_shift z B N hB).eqSymm).eqTrans
      (GaussianRationalLinearProduct.add_sub_right a w (GaussianRationalFiniteSum.sum_canonical _ _ _))
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent C C C (U C a) (U C b) (U C w) a b w
    (exponential_input C a (constant_regular a)) (exponential_input C b (constant_regular b))
    (exponential_input C w (constant_regular w)) (GaussianNamedGammaHalfShift.constant_sum a b w eq)

theorem head_shift (z R S B N : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (translated z B one) S B) : Γ ⊢[PRAAx]
    crossEquivalent leftF rightF (leftData z S B N) (rightData z R B N) := by
  let w := translated z B one
  let a := powerProduct z B N
  let b := powerProduct w B N
  let A := plain z B N
  let T := terminal z B N
  let x := expData (total z B N)
  let y := expData (total w B N)
  let u := expData (exponent z B N)
  let e := multiplierData z B N
  have hx := exp_regular (Γ := Γ) (total z B N)
  have hy := exp_regular (Γ := Γ) (total w B N)
  have hu := exp_regular (Γ := Γ) (exponent z B N)
  have he := multiply_fast C E T u (constant_regular _) hu
  have left := multiply_cross H F C C (headData w S B N) (FData w B N) A A
    (GaussianBarnesCanonicalHead.regular w S B _ N hw) (GaussianBarnesCanonicalHeadExponentialFactors.regular w B N)
    (constant_regular A) (constant_regular A) (GaussianBarnesCanonicalHeadExponentialFactors.head_cross w S B N hw)
    (cross_refl C A (constant_regular A))
  have right := multiply_cross H F F F (headData z R B N) (FData z B N) e e
    (GaussianBarnesCanonicalHead.regular z R B _ N h) (GaussianBarnesCanonicalHeadExponentialFactors.regular z B N)
    he he (GaussianBarnesCanonicalHeadExponentialFactors.head_cross z R B N h) (cross_refl F e he)
  have left_fold := collect_constants E b A y hy
  have right_split := cross_symm _ _ _ _ (multiply_associative F C E (FData z B N) T u
    (GaussianBarnesCanonicalHeadExponentialFactors.regular z B N) (constant_regular T) hu)
  have right_fold := multiply_cross (multiplyF F C) F E E (multiplyData F C (FData z B N) T)
    (multiplyData C E (qmul a T) x) u u
    (multiply_fast _ _ _ _ (GaussianBarnesCanonicalHeadExponentialFactors.regular z B N) (constant_regular T))
    (multiply_fast _ _ _ _ (constant_regular (qmul a T)) hx) hu hu
    (collect_constants E a T x hx) (cross_refl E u hu)
  have right_assoc := multiply_associative C E E (qmul a T) x u (constant_regular _) hx hu
  have right_exp := multiply_cross C C (multiplyF E E) E (qmul a T) (qmul b A) (multiplyData E E x u) y
    (constant_regular _) (constant_regular _) (multiply_fast E E x u hx hu) hy
    (constant_data_cross _ _ (power_shift z B N h.andE₁).eqSymm) (exponential_shift z B N h.andE₁)
  exact cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ left left_fold)
    (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ right (cross_trans _ _ _ _ _ _ right_split
      (cross_trans _ _ _ _ _ _ right_fold (cross_trans _ _ _ _ _ _ right_assoc right_exp)))))

theorem actual_Barnes_original_head_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     let N := var 4
     source z R B ⟶ source (translated z B one) S B ⟶ crossEquivalent leftF rightF (leftData z S B N) (rightData z R B N)) :=
  closeUniv 5 (.impI (.impI (head_shift _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadShift
