import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteIntegerDomain
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteRecurrence
import IPRADerivations.Analysis.Euler.PositiveAxis.Moments.GaussianEulerIntegerBoundary

/-!
# A fixed-precision successor estimate for the integer upper integral

Read the actual normalized recurrence into its two literal summands.
The old term retains the actual incomplete observation; the split
term is the literal rational power times the original decay sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteIntegerDomain (source data data_succ original_source)
open GaussianEulerIncompleteName (upperF original_regular_names)
open GaussianGammaFactorialValues (argument radius scalarArgument)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerIncompleteRecurrence (upperRhsF upperRhsData productF productData productCost split_regular)
open GaussianEulerIncompleteBoundary (endpointData)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (multiply_fast sum_distance)
open GaussianNameEquivalence (cross_at)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (p i a b : PTm n) : PTm n := ap2 upperF p (data i a b)
def decay (p a b : PTm n) : PTm n := ap2 decayF p (decayData a b)
def stepCost (i a b : PTm n) : PTm n :=
  productCost upperF (argument i) (radius i) one one a b+num 6+GaussianEulerIntegerBoundary.error (succ i) a b

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p i a b : PTm n) :
    Syn.subst σ (value p i a b) = value (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) := by simp [value]
@[simp] theorem subst_decay {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (decay p a b) = decay (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [decay]
@[simp] theorem subst_stepCost {m : ℕ} (σ : Fin n → PTm m) (i a b : PTm n) :
    Syn.subst σ (stepCost i a b) = stepCost (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [stepCost,productCost]

theorem original_upper_step (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (value p (succ i) a b)
      (qadd (qmul (scalarArgument i) (value p i a b))
        (qmul (GaussianEulerIntegerBoundary.monomial (succ i) a b) (decay p a b))) (stepCost i a b) (unit p) := by
  let z := argument i
  let R := radius i
  let c := scalarArgument i
  let X := data i a b
  let P := productData upperF z R one one a b
  let e := endpointData z one a b
  let V := unit p
  have hV := unit_positive (Γ := Γ) p
  have hc := constant_regular (Γ := Γ) c
  have src := original_source i a b h
  have name := (original_regular_names z R one one a b src).andE₂
  have equ := (GaussianEulerIncompleteRecurrence.original_incomplete_recurrences z R one one a b src).andE₂
  have first := cross_at _ _ _ _ p p equ
  have eqLeft : Γ ⊢[PRAAx] value p (succ i) a b ≐
      ap2 upperF p (GaussianEulerIncompleteName.data (shifted z one) (R+one) one one a b) :=
    congrAp2 upperF (.eqRefl _) (data_succ i a b)
  have reduced := distance_radius_mono _ _ _ _ two V (positive_product _ _ hV hV) hV
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr eqLeft.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) first)
  have prodReg := multiply_fast constantF upperF c X hc name
  have add := GaussianNameRingLaws.add_sample_error (productF upperF) GaussianEulerIntegrandName.nameF P e p
    prodReg (split_regular z R one one a b src)
  have prod := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p c) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (GaussianNameRingLaws.multiply_sample_error constantF upperF c X p hc name)
  have atInteger := GaussianEulerIntegerBoundary.sample_error p (succ i) a b h
  have boundEq : Γ ⊢[PRAAx] ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegerBoundary.integerData (succ i) a b) ≐
      ap2 GaussianEulerIntegrandName.nameF p e :=
    congrAp2 GaussianEulerIntegrandName.nameF (.eqRefl _) (GaussianEulerIntegerBoundary.integerData_succ i a b)
  have atSplit := distance_congr boundEq (.eqRefl _) (.eqRefl _) (.eqRefl _) atInteger
  have sum := sum_distance _ _ _ _ _ _ _ hV prod atSplit
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [stepCost,productCost,GaussianNameRingLaws.three,c,X,scalarArgument,data]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hV reduced (distance_triangle_same _ _ _ _ _ _ hV add sum))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerStep
