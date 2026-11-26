import IPRADerivations.Analysis.GaussianBinetLaplaceMomentBackwardWindow

/-!
# Uniform positive-axis variation of the original improper Binet moments

On a fixed positive margin, the sampled Taylor comparison and the
successor bound give a Lipschitz constant depending only on the order
and the margin. The right endpoint can use any original rational
chart for the same point.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentVariation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceMomentImproper (nameF data regular sample_canonical)
open GaussianBinetLaplaceMomentImproperTaylor (observation_taylor_with_cap linearSample)
open GaussianBinetLaplaceMomentMarginBound (marginBound)
open GaussianBinetLaplaceMomentRescale (rational_proper)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReconstructionRoots (distance_zero_iff)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def gain (j K : PTm n) : PTm n :=
  marginBound (succ j) K+num 3*(marginBound (succ (succ j)) K+num 3)

def input (X D R Y E S K H Q : PTm n) : Fm PTm n :=
  (realSource X zero D zero R ⋏ realSource Y zero E zero S) ⋏
    ((le one K ⋏ le D (K*X)) ⋏ (le one Q ⋏ (le H Q ⋏ (X*Q+H*D)*E ≐ Y*(D*Q))))

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (j K : PTm n) :
    Syn.subst σ (gain j K) = gain (Syn.subst σ j) (Syn.subst σ K) := by simp [gain]

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (X D R Y E S K H Q : PTm n) :
    (input X D R Y E S K H Q).subst σ =
      input (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ Y) (Syn.subst σ E)
        (Syn.subst σ S) (Syn.subst σ K) (Syn.subst σ H) (Syn.subst σ Q) := by simp [input,one]

theorem gain_positive (j K : PTm n) : Γ ⊢[PRAAx] le one (gain j K) := by
  have h : Γ ⊢[PRAAx] le one (num 11 : PTm n) := by ipra_le 10
  exact le_trans h (le_trans (le_add_left _ _) (le_add_right _ _))

theorem ordered_observations (p j X D R Y E S K H Q : PTm n)
    (h : Γ ⊢[PRAAx] input X D R Y E S K H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j Y E S)) (ap2 nameF p (data j X D R))
      (diagonalNumerator (gain j K*H) Q (num 12) p) (diagonalDenominator Q p) := by
  let A := X*Q+H*D
  let B := D*Q
  let U := unit p
  let y := ap2 nameF p (data j Y E S)
  let x := ap2 nameF p (data j X D R)
  let z := ap2 nameF p (data (succ j) X D R)
  let w := radiusPoint H Q
  let M := marginBound (succ j) K
  let N := marginBound (succ (succ j)) K+num 3
  have hBase := h.andE₁.andE₁
  have hEnd := h.andE₁.andE₂
  have hD := hBase.andE₁.andE₂
  have hX := hBase.andE₁.andE₁.andE₁
  have hK := h.andE₂.andE₁.andE₁
  have hMargin := h.andE₂.andE₁.andE₂
  have hQ := h.andE₂.andE₂.andE₁
  have hh := h.andE₂.andE₂.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hQ hp
  have den₂ := positive_product _ _ (positive_product _ _ hQ hQ) hp
  have shifted : Γ ⊢[PRAAx] realSource A zero B zero (radius A zero) :=
    source_of_right_half_plane _ _ _ _
      (.andI (.andI (le_trans (positive_product _ _ hX hQ) (le_add_right _ _)) (.orI₁ (.eqRefl zero)))
        (positive_product _ _ hD hQ))
  have cross := GaussianNameEquivalence.cross_at nameF nameF (data j Y E S) (data j A B (radius A zero)) p p
    (rational_proper j Y E S A B (radius A zero) hEnd shifted h.andE₂.andE₂.andE₂.andE₂.eqSymm)
  have chart : Γ ⊢[PRAAx] distanceBounded y (ap2 nameF p (data j A B (radius A zero))) (two*Q) (Q*U) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) den
      (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) cross
  have higher := GaussianBinetLaplaceMomentMarginBound.observation_bound p (succ (succ j)) X D R K hBase hK hMargin
  have taylor := observation_taylor_with_cap p j X D R (radius A zero) H Q _ hBase shifted hQ hh higher
  have approximation : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j A B (radius A zero))) (qsub x (qmul w z))
      (num 3*H*N*U+num 10*Q) (Q*U) :=
    distance_radius_mono _ _ _ _ _ _ den₂ den
      (by dsimp only [N,U]; ipra_le 3*𝔞(H)*𝔞(marginBound (succ (succ j)) K+num 3)*𝔞(Q)*𝔞(unit p)*𝔞(unit p)*sl hh) taylor
  have next := GaussianBinetLaplaceMomentMarginBound.observation_bound p (succ j) X D R K hBase hK hMargin
  have norm := bounded_product w z H Q M one hQ (le_refl one) (radius_bounded H Q hQ) next
  have toZero : Γ ⊢[PRAAx] distanceBounded (qmul w z) qzero (H*M) Q :=
    (distance_zero_iff _ _ _ hQ).iffMpr (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) norm)
  have translated : Γ ⊢[PRAAx] distanceBounded (qsub x (qmul w z)) x (H*M) Q :=
    distance_congr (.eqRefl _) (GaussianRationalReconstruction.qsub_zero_right x (sample_canonical p j X D R))
      (zero_add _) (.eqRefl _)
      (GaussianNamedDifference.difference_distance x x _ qzero zero _ Q hQ
        (GaussianRationalPowerDifference.distance_refl_zero x Q hQ) toZero)
  have changeClock := distance_radius_mono _ _ _ _ (H*M*U) (Q*U) hQ den
    (le_of_eq_add (d := zero) (by ipra_ring)) translated
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [diagonalNumerator,gain,M,N,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den (distance_triangle_same _ _ _ _ _ _ den chart approximation) changeClock)

theorem ordered_rate (j X D R Y E S K H Q : PTm n) (h : Γ ⊢[PRAAx] input X D R Y E S K H Q) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data j Y E S) (data j X D R) (gain j K*H) Q := by
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF (data j Y E S) (data j X D R)
    (gain j K*H) Q (num 12) h.andE₂.andE₂.andE₁
    (regular _ _ _ _ h.andE₁.andE₂) (regular _ _ _ _ h.andE₁.andE₁)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] input (s X) (s D) (s R) (s Y) (s E) (s S) (s K) (s H) (s Q) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_input] using h.shift
  change Δ ⊢[PRAAx] distanceBounded (ap2 nameF (var 0) (Syn.shift (data j Y E S)))
    (ap2 nameF (var 0) (Syn.shift (data j X D R)))
    (diagonalNumerator (Syn.shift (gain j K*H)) (s Q) (Syn.shift (num 12)) (var 0))
    (diagonalDenominator (s Q) (var 0))
  rw [show Syn.shift (data j Y E S) = data (s j) (s Y) (s E) (s S) from GaussianBinetLaplaceMomentImproper.subst_data _ _ _ _ _,
    show Syn.shift (data j X D R) = data (s j) (s X) (s D) (s R) from GaussianBinetLaplaceMomentImproper.subst_data _ _ _ _ _,
    show Syn.shift (gain j K*H) = gain (s j) (s K)*s H by simp only [Syn.shift,s,subst_gain,PTm.subst_mul],
    show Syn.shift (num 12 : PTm n) = num 12 by simp only [Syn.shift,PTm.subst_num]]
  exact ordered_observations (var 0) (s j) (s X) (s D) (s R) (s Y) (s E) (s S) (s K) (s H) (s Q) hs

theorem actual_improper_Binet_moment_ordered_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let j := var 0
     let X := var 1
     let D := var 2
     let R := var 3
     let Y := var 4
     let E := var 5
     let S := var 6
     let K := var 7
     let H := var 8
     let Q := var 9
     input X D R Y E S K H Q ⟶ independentRate nameF nameF (data j Y E S) (data j X D R) (gain j K*H) Q) :=
  closeUniv 10 (.impI (ordered_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentVariation
