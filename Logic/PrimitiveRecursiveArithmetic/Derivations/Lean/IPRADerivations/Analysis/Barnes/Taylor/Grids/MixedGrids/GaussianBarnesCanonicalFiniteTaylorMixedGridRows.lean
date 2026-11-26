import IPRADerivations.Analysis.Barnes.Taylor.Grids.MixedGrids.GaussianBarnesCanonicalCofinalTaylorMixedGridRows

/-!
# Mixed rows of an actual fixed Barnes partial product

Both grids use the same literal cutoff and one Taylor polynomial.
Each backward row is written at its exact displacement from the
original center before applying the finite Taylor estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridRows

open_ipra
open ComplexLogarithmRemainder (add bounded scale)
open GaussianBarnesCanonicalCofinalTaylorMixedGridRows (literal_node_error polynomialGrid productCap rowNumerator)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid literal_at)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (rowNumeratorWithGains rowDenominator row_denominator_positive)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalMixedTaylorGridGeometry
  (native_associative forward_bound backward_bound forward_point backward_point backwardDisplacement)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit)
open GaussianPolynomialForwardDifferenceGrid (point)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian qzero)
open GaussianRationalMetric (distanceBounded qnegative)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "gneg" => ComplexLogarithmRemainder.neg

local notation "literal" => GaussianBarnesCanonicalProduct.literalData

theorem backward_literal (z h R B r j : PTm n) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFiniteTaylorGrid.literalData (add z h) (gneg h) R B r j ≐
      literal (add z (backwardDisplacement h j)) (R+one) B (initial (R+one)+r) := by
  ipra_congr (literal (var 0) (var 1) (var 2) (var 3) : PTm 4)
    with [native_associative z h (scale j (gneg h)), .eqRefl (R+one), .eqRefl B, .eqRefl (initial (R+one)+r)]
    using [GaussianBarnesCanonicalFiniteTaylorGrid.literalData,backwardDisplacement]

theorem node_error (t q z δ R B H r M x k j : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B)
    (hδ : Γ ⊢[PRAAx] bounded δ (previous M*H))
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*H)) B)
    (hj : Γ ⊢[PRAAx] lt j (succ (previous M)))
    (hp : Γ ⊢[PRAAx] ofGaussian δ B ≐ point x k j) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V t (literal (add z δ) (R+one) B (initial (R+one)+r)))
      (entry (polynomialGrid t q z R B H r M x k) j)
      (rowNumerator t q z R B H r M x k) (rowDenominator q t B M) := by
  let J := pw B (succ (previous M))
  let D := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M
  let E := rowDenominator q t B M
  have hE := row_denominator_positive q t B M hz.andE₁
  have fit : Γ ⊢[PRAAx] le
      (rowNumeratorWithGains q t B H M (two+productCap q z R B H r M x k) (analyticGain R M) (clockGain R))
      (rowNumerator t q z R B H r M x k) :=
    le_of_eq_add (d := J*unit t+D*two) (by
      dsimp only [rowNumerator,rowNumeratorWithGains,D,J]
      ipra_ring)
  exact distance_radius_mono _ _ _ _ _ _ hE hE (mul_le_mul_right E fit)
    (literal_node_error t q z δ R B H r M x k j hz hδ hs hj hp)

theorem forward_rows (t q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H)
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*H))) B) :
    Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r (previous M))
      (polynomialGrid t q z R B (two*H) r M qzero (ofGaussian h B)) (succ (previous M))
      (rowNumerator t q z R B (two*H) r M qzero (ofGaussian h B)) (rowDenominator q t B M) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let j : PTm (n+1) := var 0
  let N := previous (a M)
  let Δ := lt j (succ N) :: Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
  have h' : Δ ⊢[PRAAx] bounded (a h) (a H) := by simpa [Δ,a,Fm.shift,Syn.shift] using hh.shift.wk
  have s' : Δ ⊢[PRAAx] le (stepDivisor (a R)*(N*(two*a H))) (a B) := by
    simpa [Δ,a,N,Fm.shift,Syn.shift,two] using hs.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (succ N) := Prf.hyp0
  have row := node_error (a t) (a q) (a z) (scale j (a h)) (a R) (a B) (two*a H) (a r) (a M) qzero
    (ofGaussian (a h) (a B)) j z' (forward_bound _ _ _ _ h' (Common.le_of_lt_succ hj))
    s' hj (forward_point _ _ _ z'.andE₁)
  have read := literal_at (a t) (a z) (a h) (a R) (a B) (a r) N j hj
  simpa [Δ,a,j,N,Syn.shift,one,two] using distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) row

theorem backward_rows (t q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H)
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*H))) B) :
    Γ ⊢[PRAAx] rowBound (literalGrid t (add z h) (gneg h) R B r (previous M))
      (polynomialGrid t q z R B (two*H) r M (ofGaussian h B) (qnegative (ofGaussian h B))) (succ (previous M))
      (rowNumerator t q z R B (two*H) r M (ofGaussian h B) (qnegative (ofGaussian h B))) (rowDenominator q t B M) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let j : PTm (n+1) := var 0
  let N := previous (a M)
  let Δ := lt j (succ N) :: Γ.map Fm.shift
  let w := ofGaussian (a h) (a B)
  have z' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
  have h' : Δ ⊢[PRAAx] bounded (a h) (a H) := by simpa [Δ,a,Fm.shift,Syn.shift] using hh.shift.wk
  have s' : Δ ⊢[PRAAx] le (stepDivisor (a R)*(N*(two*a H))) (a B) := by
    simpa [Δ,a,N,Fm.shift,Syn.shift,two] using hs.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (succ N) := Prf.hyp0
  have hN : Δ ⊢[PRAAx] le one N := zero_lt_succ _
  have row := node_error (a t) (a q) (a z) (backwardDisplacement (a h) j) (a R) (a B)
    (two*a H) (a r) (a M) w (qnegative w) j z'
    (backward_bound _ _ _ _ h' hN (Common.le_of_lt_succ hj)) s' hj (backward_point _ _ _ z'.andE₁)
  have read := (literal_at (a t) (add (a z) (a h)) (gneg (a h)) (a R) (a B) (a r) N j hj).eqTrans
    (congrAp2 V (.eqRefl _) (backward_literal (a z) (a h) (a R) (a B) (a r) j))
  simpa [Δ,a,j,N,w,Syn.shift,one,two] using distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) row

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridRows
