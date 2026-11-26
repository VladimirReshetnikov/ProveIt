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
open ComplexLogarithmRemainder (add bounded bounded_mono scale)
open GaussianBarnesCanonicalCofinalTaylorMixedGridRows (polynomialGrid productCap rowNumerator)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid literal_at)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData finite_regular)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorGrid (polynomial)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (cap cost_le_cap scaledPolynomial)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (rowNumeratorWithGains rowDenominator row_denominator_positive)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalMixedTaylorGridGeometry
  (native_associative forward_bound backward_bound forward_point backward_point backwardDisplacement)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyData multiplyModulus)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianPolynomialForwardDifferenceGrid (point samples sample_lookup)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalCoefficientScaling (scaled evaluation_linearity)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (evaluate ofGaussian positive_product qmul qzero)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "C" => GaussianBarnesCanonicalFiniteWeightedTaylorValue.nameF
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
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
  let S := R+one
  let N := previous M
  let P := polynomial q z R B H r M N
  let d := finiteData z S B r
  let c := ap2 finiteNameF t d
  let α := samples P (succ N) x k
  let v := entry α j
  let y := point x k j
  let L := multiplyModulus finiteNameF constantF d v+one
  let K := productCap q z R B H r M x k
  let A := GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.numerator q S B (N*H) M
  let D := GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q S B M
  let D' := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M
  let U := unit t
  let Q := unit q
  let J := pw B (succ N)
  let A' := GaussianBarnesCanonicalFiniteTaylorGridBudget.numeratorWithCaps q S B H M
    (GaussianBarnesCanonicalHeadUniformMass.headCap S) (GaussianBarnesCanonicalFiniteCentralDiskBound.cap S)
  have z' : Γ ⊢[PRAAx] source z S B :=
    .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by dsimp only [S]; ipra_ring)))
  have finite := GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.shared_rate q z δ R B (N*H) r M hz hδ hs
  have step₂ := rate_at _ _ _ _ _ _ t t finite
  have cmp : Γ ⊢[PRAAx] le (A*D') (A'*D) :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.radius_comparison_with_caps q S B H M _ _
  have pos : Γ ⊢[PRAAx] le one D' :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator_positive q B M hz.andE₁
  have hd : Γ ⊢[PRAAx] le one D :=
    GaussianBarnesCanonicalFiniteTaylorGrid.denominator_positive q R B M hz.andE₁
  have hsamp : Γ ⊢[PRAAx] evaluate P (ofGaussian δ B) ≐ v :=
    (GaussianRationalReconstruction.evaluate_congr (.eqRefl P) hp).eqTrans
      (sample_lookup P (succ N) x k j hj).eqSymm
  have pd : Γ ⊢[PRAAx] GaussianBarnesCanonicalFiniteWeightedTaylorValue.data q z δ S B (N*H) r M ≐
      multiplyData finiteNameF constantF d v := by
    ipra_congr (multiplyData finiteNameF constantF (var 0) (var 1) : PTm 2) with [.eqRefl d, hsamp]
      using [GaussianBarnesCanonicalFiniteWeightedTaylorValue.data, P, polynomial, d, S, N]
  have product := GaussianNameRingLaws.multiply_sample_error finiteNameF constantF d v t
    (finite_regular z S B r z') (constant_regular v)
  have eval : Γ ⊢[PRAAx] qmul c (ap2 constantF t v) ≐ entry (polynomialGrid t q z R B H r M x k) j :=
    (qmul_congr (.eqRefl c) ((constant_at t v).eqTrans (sample_lookup P (succ N) x k j hj))).eqTrans
      ((evaluation_linearity P c y).eqSymm.eqTrans (sample_lookup (scaled P c) (succ N) x k j hj).eqSymm)
  have step₃ := distance_congr (congrAp2 C (.eqRefl t) pd).eqSymm eval (.eqRefl _) (.eqRefl _) product
  have Epos := row_denominator_positive q t B M hz.andE₁
  have bound : Γ ⊢[PRAAx] le L K := cost_le_cap d α N j hj
  have hleft : Γ ⊢[PRAAx] L*(D'*U) ≐ L*rowDenominator q t B M := .eqRefl _
  have hright : Γ ⊢[PRAAx] K*(D'*U) ≐ (D'*K)*U := by ipra_ring
  have paid := distance_radius_mono _ _ _ _ (D'*K) (rowDenominator q t B M) (unit_positive t) Epos
    (le_congr hleft hright (mul_le_mul_right (D'*U) bound)) step₃
  have first : Γ ⊢[PRAAx] distanceBounded
      (ap2 V t (literal (add z δ) S B (initial S+r)))
      (ap2 C t (GaussianBarnesCanonicalFiniteWeightedTaylorValue.data q z δ S B (N*H) r M))
      (A'*U+D'*two) (rowDenominator q t B M) :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hd) Epos
      (by
        change Γ ⊢[PRAAx] le ((A*U*U+D*(U+U))*(D'*U)) ((A'*U+D'*two)*(D*U*U))
        ipra_le 𝔞(U)*𝔞(U)*𝔞(U)*sl cmp) step₂
  have sum := distance_triangle_same _ _ _ _ _ _ Epos first paid
  have fit : Γ ⊢[PRAAx] le (A'*U+D'*two+D'*K) (rowNumerator t q z R B H r M x k) :=
    le_of_eq_add (d := J*U+D'*two) (by
      dsimp only [rowNumerator,rowNumeratorWithGains,A',D',analyticGain,clockGain,
        GaussianBarnesCanonicalFiniteTaylorGridBudget.numeratorWithCaps,
        GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator,J,Q,U,K]
      ipra_ring)
  exact distance_radius_mono _ _ _ _ _ _ Epos Epos (mul_le_mul_right (rowDenominator q t B M) fit) sum

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
