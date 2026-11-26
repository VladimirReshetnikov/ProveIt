import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherQuartic
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilySplit

/-!
# Original finite Glaisher logarithm approximants

The actual finite named sum uses original mesh logarithms for the terms
`j*log(j)`. The finite approximant adds the two explicit contributions
`-((6*N^2+6*N+1)/12)*log(N)` and `N^2/4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherFinite

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent)
open GaussianPositiveRationalLogarithm (baseF)
open GaussianBarnesGlaisherQuartic (negativeWeight weightNumerator correction)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical represents
  represents_congr represents_rescale positive_product qadd qadd_represents qadd_canonical canonical_unique)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "neg" => ComplexLogarithmRemainder.neg

def weightedF : PR 2 := multiplyF constantF baseF
def weightedData (a j : PTm n) : PTm n := multiplyData constantF baseF a j
def row (j : PTm n) : PTm n := weightedData (naturalPoint j) j
def body : PTm 2 := row (succ (var 0))
def sumF : PR 2 := GaussianNamedFiniteSumFamily.nameF weightedF body
def sumData (N : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data N zero
def squareQuarter (N : PTm n) : PTm n := ofGaussian (scale (N*N) oneCode) (num 4)
def nameF : PR 2 := addF (addF sumF weightedF) constantF
def data (N : PTm n) : PTm n :=
  addData (addData (sumData N) (weightedData (negativeWeight N) N)) (squareQuarter N)

theorem weighted_regular (a j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] pointCN weightedF (weightedData a j) :=
  multiply_fast constantF baseF a j (constant_regular a) (GaussianGammaFiniteApproximantName.log_regular j hj)

theorem body_at (i x : PTm n) : inst2 body i x = row (succ i) := by
  simp [body,row,weightedData,inst2]

theorem regular_rows (N x : PTm n) : Γ ⊢[PRAAx] GaussianNamedFiniteProductFamily.regularRows weightedF body N x := by
  refine .allI (.impI ?_)
  rw [body_at]
  exact weighted_regular _ _ (zero_lt_succ _)

theorem sum_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN sumF (sumData N) :=
  GaussianNamedFiniteSumFamily.regular weightedF body N zero (regular_rows N zero)

theorem regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN nameF (data N) :=
  add_fast _ _ _ _ (add_fast _ _ _ _ (sum_regular N) (weighted_regular _ _ hN)) (constant_regular _)

theorem sum_append (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent sumF (addF sumF weightedF) (sumData (succ N)) (addData (sumData N) (row (succ N))) := by
  simpa only [body_at,sumF,sumData] using
    GaussianNamedFiniteSumFamilySplit.append_cross weightedF body N zero (regular_rows (succ N) zero)

theorem weight_step (N : PTm n) : Γ ⊢[PRAAx]
    qadd (naturalPoint (succ N)) (negativeWeight (succ N)) ≐ negativeWeight N := by
  let a := scale (num 12) (scale (succ N) oneCode)
  let b := neg (scale (weightNumerator (succ N)) oneCode)
  let c := neg (scale (weightNumerator N) oneCode)
  let D : PTm n := num 12
  have hd : Γ ⊢[PRAAx] le one D := zero_lt_succ (num 11)
  have left : Γ ⊢[PRAAx] represents (naturalPoint (succ N)) a D :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul _)
      (represents_rescale _ _ _ D (natural_point_represents _))
  have right : Γ ⊢[PRAAx] represents (negativeWeight (succ N)) b D := ofGaussian_represents _ _ hd
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add a b) c := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [a,b,c,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_neg,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,weightNumerator]
      ipra_simps
      ring
    · simp only [a,b,c,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_neg,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
      ring
  exact canonical_unique _ _ c D (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) eq (.eqRefl _) (qadd_represents _ _ _ _ _ hd left right))
    (ofGaussian_represents _ _ hd)

theorem quarter_step (N : PTm n) : Γ ⊢[PRAAx]
    qadd (squareQuarter N) (correction N) ≐ squareQuarter (succ N) := by
  let a := scale (N*N) oneCode
  let b := scale (two*N+one) oneCode
  let c := scale (succ N*succ N) oneCode
  let D : PTm n := num 4
  have hd : Γ ⊢[PRAAx] le one D := zero_lt_succ (num 3)
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add a b) c := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [a,b,c,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
      ipra_simps
      ring
    · simp only [a,b,c,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
      ring
  have raw := qadd_represents _ _ _ _ _ hd (ofGaussian_represents a D hd) (ofGaussian_represents b D hd)
  exact canonical_unique _ _ c D (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) eq (.eqRefl _) raw) (ofGaussian_represents _ _ hd)

theorem actual_Glaisher_finite_logarithm_approximant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ pointCN nameF (data (var 0))) :=
  closeUniv 1 (.impI (regular _ Prf.hyp0))

theorem actual_Glaisher_weighted_prefix_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent sumF (addF sumF weightedF) (sumData (succ (var 0))) (addData (sumData (var 0)) (row (succ (var 0))))) :=
  closeUniv 1 (sum_append _)

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherFinite
