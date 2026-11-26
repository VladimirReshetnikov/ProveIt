import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetLogCellGrid
import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmRescale
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Integration.GaussianRationalPanelTailDistance

/-!
# The sharp named logarithm error on a horizontal unit cell

Refine the actual logarithm mesh and its observation clock together.
The mesh and clock errors tend to zero, leaving exactly the difference
of the positive real reciprocals that bounds the finite tagged average.
-/

set_option autoImplicit false
set_option maxHeartbeats 330000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLogCellComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLogCellGrid (endpoint finite_grid requiredMesh)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget distance_difference_same)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianLogGammaEulerHead (argument shifted_source)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianNameEquivalence (cross_at cross_symm point_at)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (reciprocal)
open GaussianRightHalfPlaneLogarithm (source)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data

def nameF : PR 2 := GaussianNamedDifference.nameF L L

def data (A B D neg k : PTm n) : PTm n :=
  GaussianNamedDifference.data (ld (A+(k+one)*D) B D neg) (ld (A+k*D) B D neg)

def leftValue (A B D neg k : PTm n) : PTm n := reciprocal (shiftedPoint (argument A B D neg) k)

def budget (A D k : PTm n) : PTm n := (A+k*D)*(A+(k+one)*D)

def precisionCost (D : PTm n) : PTm n := num 4*D*D+two

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg k : PTm n) :
    Syn.subst σ (data A B D neg k) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) := by
  simp [data, one]

@[simp] theorem subst_leftValue {m : ℕ} (σ : Fin n → PTm m) (A B D neg k : PTm n) :
    Syn.subst σ (leftValue A B D neg k) = leftValue (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) := by simp [leftValue]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (A D k : PTm n) :
    Syn.subst σ (budget A D k) = budget (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ k) := by simp [budget, one]

theorem budget_positive (A D k neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx] le one (budget A D k) :=
  positive_product _ _ (shifted_source k A D neg h).andE₁.andE₁ (shifted_source (k+one) A D neg h).andE₁.andE₁

theorem regular (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx] pointCN nameF (data A B D neg k) :=
  GaussianNamedDifference.name_regular L L _ _
    (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ (shifted_source (k+one) A D neg h))
    (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ (shifted_source k A D neg h))

private theorem rescaled_observation (p A B D neg M : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded (ap2 L p (ld A B D neg)) (ap2 L p (ld (M*A) (M*B) (M*D) neg)) two (unit p) := by
  have u := unit_positive (Γ := Γ) p
  have e := GaussianRightHalfPlaneLogarithmRescale.rescale A B D neg M h hM
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ u u) u (by ipra_le 0)
    (cross_at L L _ _ p p (cross_symm L L _ _ e))

private theorem scaled_endpoint_error (p s A B D neg k M : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data A B D neg k)) (endpoint s A B D neg k M)
      (unit s+num 11*unit p) (unit p*unit s) := by
  let x := ld (A+(k+one)*D) B D neg
  let y := ld (A+k*D) B D neg
  let X := ld (M*(A+(k+one)*D)) (M*B) (M*D) neg
  let Y := ld (M*(A+k*D)) (M*B) (M*D) neg
  let a := ap2 nameF p (data A B D neg k)
  let b := ap2 nameF s (data A B D neg k)
  let c := qsub (ap2 L s x) (ap2 L s y)
  let d := endpoint s A B D neg k M
  let U := unit p
  let V := unit s
  let Z := U*V
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) s
  have hz : Γ ⊢[PRAAx] le one Z := positive_product _ _ hu hv
  have fx := shifted_source (k+one) A D neg h
  have fy := shifted_source k A D neg h
  have first : Γ ⊢[PRAAx] distanceBounded a b (U+V) Z :=
    point_at nameF _ p s (regular A B D neg k h)
  have second : Γ ⊢[PRAAx] distanceBounded b c (num 6) V :=
    GaussianNamedDifference.sample_error L L x y s
      (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ fx) (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ fy)
  have third : Γ ⊢[PRAAx] distanceBounded c d (two+two) V :=
    distance_difference_same (ap2 L s x) (ap2 L s y) (ap2 L s X) (ap2 L s Y) two two V hv
      (rescaled_observation s _ B D neg M fx hM) (rescaled_observation s _ B D neg M fy hM)
  have near := distance_triangle_same b c d (num 6) (two+two) V hv second third
  have placed := distance_radius_mono b d _ V (num 10*U) Z hv hz (by dsimp only [Z]; ipra_le 0) near
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [U,V]; ipra_ring) (.eqRefl _)
    (distance_triangle_same a b d (U+V) (num 10*U) Z hz first placed)

private theorem diagonal (p A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data A B D neg k)) (ap2 constantF p (leftValue A B D neg k))
      (diagonalNumerator (D*D) (budget A D k) (precisionCost D) p) (diagonalDenominator (budget A D k) p) := by
  let U := unit p
  let M := requiredMesh A B D k+U
  let C := num 9*M+num 11
  let t := exponent C p
  let V := unit t
  let X := A+k*D
  let W := M*(X*X)
  let D₀ := U*W*V
  let E := budget A D k
  let a := ap2 nameF p (data A B D neg k)
  let b := endpoint t A B D neg k M
  let c := GaussianBinetReciprocalMean.value A B D neg k M
  let d := leftValue A B D neg k
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) t
  have hm : Γ ⊢[PRAAx] le one M := le_trans hu (le_add_left _ _)
  have hx : Γ ⊢[PRAAx] le one X := (shifted_source k A D neg h).andE₁.andE₁
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ hm (positive_product _ _ hx hx)
  have hD₀ : Γ ⊢[PRAAx] le one D₀ := positive_product _ _ (positive_product _ _ hu hW) hv
  have hE : Γ ⊢[PRAAx] le one E := budget_positive A D k neg h
  have mCost : Γ ⊢[PRAAx] le U W := by
    unfold W M
    have sq := positive_product X X hx hx
    ipra_le sl sq*(𝔞(requiredMesh A B D k)+𝔞(U))+𝔞(requiredMesh A B D k)
  have vCost : Γ ⊢[PRAAx] le (C*U) V := query_budget C p
  have scaled := scaled_endpoint_error p t A B D neg k M h hm
  have grid : Γ ⊢[PRAAx] distanceBounded b c (num 4*D*D*V+num 9*(M*M)*(X*X)) (W*V) :=
    finite_grid t A B D neg k M h hm (le_add_right _ _)
  have first := distance_radius_mono a b _ (U*V) ((V+num 11*U)*W) D₀ (positive_product _ _ hu hv) hD₀
    (by dsimp only [D₀]; ipra_le 0) scaled
  have second := distance_radius_mono b c _ (W*V) ((num 4*D*D*V+num 9*(M*M)*(X*X))*U) D₀
    (positive_product _ _ hW hv) hD₀ (by dsimp only [D₀,W]; ipra_le 0) grid
  have sum := distance_triangle_same a b c _ _ D₀ hD₀ first second
  have small := distance_radius_mono a c _ D₀ (precisionCost D) U hD₀ hu (by
    dsimp only [D₀,precisionCost]
    have coef : Γ ⊢[PRAAx] le ((num 4*D*D*V+num 9*(M*M)*(X*X))*U+(V+num 11*U)*W)
        ((num 4*D*D+two)*W*V) := by
      have mCost' : Γ ⊢[PRAAx] le U (M*(X*X)) := mCost
      have vCost' : Γ ⊢[PRAAx] le ((num 9*M+num 11)*U) V := vCost
      dsimp only [W]
      ipra_le 4*𝔞(D)^2*𝔞(V)*sl mCost'+𝔞(M*(X*X))*sl vCost'
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right U coef)) sum
  have mean := GaussianBinetReciprocalMean.finite_mean_distance A B D neg k M h hm
  have joined := GaussianRationalPanelTailDistance.triangle a c d _ _ _ _ hu hE small mean
  exact distance_congr (.eqRefl _) (constant_at p d).eqSymm
    (by dsimp only [E,U,diagonalNumerator]; ipra_ring)
    (by dsimp only [E,U,diagonalDenominator]; ipra_ring) joined

theorem independent_rate (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data A B D neg k) (leftValue A B D neg k) (D*D) (budget A D k) := by
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (precisionCost D) (budget_positive A D k neg h)
    (regular A B D neg k h) (constant_regular _) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let s (v : PTm n) := Syn.shift v
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa only [diagonalEnvelope, Syn.shift, s, Δ, subst_data, subst_budget, subst_leftValue, PTm.subst_mul,
    precisionCost, PTm.subst_add, PTm.subst_num, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    diagonal (var 0) (s A) (s B) (s D) (s neg) (s k) hs

theorem actual_complex_logarithm_rectangle_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ independentRate nameF constantF
      (data (var 0) (var 1) (var 2) (var 3) (var 4)) (leftValue (var 0) (var 1) (var 2) (var 3) (var 4))
      (var 2*var 2) (budget (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (independent_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLogCellComparison
