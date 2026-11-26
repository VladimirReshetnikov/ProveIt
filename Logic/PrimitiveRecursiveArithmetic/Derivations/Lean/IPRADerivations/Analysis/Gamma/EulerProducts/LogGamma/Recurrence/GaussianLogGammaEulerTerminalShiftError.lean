import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualCanonicalError
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmRescale
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTATelescope
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# Terminal logarithm error in the finite Euler unit shift

Split `Log(z + N + 1)` into the real logarithm of `N` and the original
right-half-plane residual. Its finite observation has error at most
`2S/N + 8/2^p`, where `S` is the computed radius of `z + 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTerminalShiftError

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerHead (shifted_source)
open GaussianLogGammaEulerResidualCanonicalError (canonicalPoint canonical_sample_error)
open GaussianLogGammaEulerResidualDomain (linearTerm linear_bound)
open GaussianLogGammaEulerResidualRadius (radius radius_positive source_of_right_half_plane)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_at)
open GaussianNameRingLaws (add_sample_error)
open GaussianPositiveRationalLogarithm (logF name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianRightHalfPlaneLogarithm (source subst_data)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data

private theorem terminal_data (A B D neg N : PTm n) :
    Γ ⊢[PRAAx] P (A + succ N * D) B D neg ≐ P ((A + D) + N * D) B D neg := by
  have shift : Γ ⊢[PRAAx] A + succ N * D ≐ (A + D) + N * D := by ipra_ring
  simpa only [subst_data, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (P (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![A + succ N * D, B, D, neg]) (σ' := ![(A + D) + N * D, B, D, neg]) (fun i => by
        fin_cases i
        · exact shift
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _)

private theorem residual_bound (p C B D neg N : PTm n) (h : Γ ⊢[PRAAx] source C D neg)
    (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (num 8 * radius C B) N) :
    Γ ⊢[PRAAx] bounded (canonicalPoint p C B D neg N)
      (num 2 * radius C B * unit p + num 3 * N) (N * unit p) := by
  let S := radius C B
  let u := unit p
  let q := N * u
  let r := canonicalPoint p C B D neg N
  let l := linearTerm C B D neg N
  let e := S * u + num 3 * N
  have hu : Γ ⊢[PRAAx] le one u := unit_positive p
  have hq : Γ ⊢[PRAAx] le one q := positive_product _ _ hN hu
  have hd := positive_product _ _ (positive_product _ _ hN hN) hu
  have hs := source_of_right_half_plane C B D neg h
  have eight : Γ ⊢[PRAAx] le one (num 8) := le_of_eq_add (d := num 7) (by ipra_ring)
  have hSN : Γ ⊢[PRAAx] le S N :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono eight (le_refl S))) hlarge
  have cmp : Γ ⊢[PRAAx] le ((S * S * u + num 3 * (N * N)) * q) (e * (N * N * u)) := by
    have base := add_le_add₂ (le_mul_mono (le_refl (S * u * q)) hSN)
      (le_refl (num 3 * (N * N) * q))
    exact le_congr (by dsimp only [q]; ipra_ring) (by dsimp only [e, q]; ipra_ring) base
  have close : Γ ⊢[PRAAx] distanceBounded r l e q :=
    distance_radius_mono r l _ _ e q hd hq cmp (canonical_sample_error p C B D neg S N hs hN hlarge)
  have linear : Γ ⊢[PRAAx] distanceBounded l qzero (S * u) q :=
    distance_radius_mono l qzero S N _ _ hN hq
      (le_of_eq_add (d := zero) (by dsimp only [q]; ipra_ring))
      ((distance_zero_iff l S N hN).iffMpr (linear_bound C B D neg S N hs hN))
  exact (distance_zero_iff r _ q hq).iffMp
    (distance_congr (.eqRefl r) (.eqRefl _) (by dsimp only [e]; ipra_ring) (.eqRefl q)
      (distance_triangle_same r l qzero e (S * u) q hq close linear))

/-- Direct common-precision bound for the original terminal logarithm and `log(N)`. -/
theorem terminal_sample_error (p A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hlarge : Γ ⊢[PRAAx] le (num 8 * radius (A + D) B) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (P (A + succ N * D) B D neg)) (ap2 logF p (L N one))
      (num 2 * radius (A + D) B * unit p + num 8 * N) (N * unit p) := by
  let C := A + D
  let S := radius C B
  let u := unit p
  let q := N * u
  let x := P (C + N * D) B D neg
  let y := L N one
  let r := P (C + N * D) B (D * N) neg
  let a := ap2 G p x
  let b := ap2 (addF logF G) p (addData y r)
  let c := ap2 logF p y
  let d := qadd c (ap2 G p r)
  let e := num 2 * S * u + num 3 * N
  have hC : Γ ⊢[PRAAx] source C D neg :=
    .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right A D)) h.andE₁.andE₂) h.andE₂
  have eight : Γ ⊢[PRAAx] le one (num 8) := le_of_eq_add (d := num 7) (by ipra_ring)
  have hN : Γ ⊢[PRAAx] le one N :=
    le_trans (positive_product _ _ eight (radius_positive C B D neg hC)) hlarge
  have hu : Γ ⊢[PRAAx] le one u := unit_positive p
  have hq : Γ ⊢[PRAAx] le one q := positive_product _ _ hN hu
  have split := GaussianRightHalfPlaneLogarithmRescale.split_shift C B D neg N hC hN
  have near : Γ ⊢[PRAAx] distanceBounded a b (num 2 * N) q :=
    distance_radius_mono a b (u + u) (u * u) _ _ (positive_product _ _ hu hu) hq
      (le_of_eq_add (d := zero) (by dsimp only [q]; ipra_ring))
      (cross_at G (addF logF G) x (addData y r) p p split)
  have hr := GaussianRightHalfPlaneLogarithm.regular (C + N * D) B (D * N) neg
    (.andI (shifted_source N C D neg hC).andE₁ (positive_product D N h.andE₂ hN))
  have observe : Γ ⊢[PRAAx] distanceBounded b d (num 3 * N) q :=
    distance_radius_mono b d _ u _ q hu hq
      (le_of_eq_add (d := zero) (by dsimp only [q, GaussianNameRingLaws.three]; ipra_ring))
      (add_sample_error logF G y r p (name_regular N one (.andI hN (le_refl one))) hr)
  have small : Γ ⊢[PRAAx] distanceBounded d c e q :=
    GaussianGeneralFTATelescope.add_increment_distance c (ap2 G p r) e q
      (residual_bound p C B D neg N hC hN hlarge)
  have sum := distance_triangle_same a d c (num 2 * N + num 3 * N) e q hq
    (distance_triangle_same a b d _ _ q hq near observe) small
  exact distance_congr (congrAp2 G (.eqRefl p) (terminal_data A B D neg N).eqSymm) (.eqRefl c)
    (by dsimp only [e]; ipra_ring) (.eqRefl q) sum

theorem actual_finite_Euler_terminal_unit_shift_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 1) (var 3) (var 4) ⟶ le (num 8 * radius (var 1 + var 3) (var 2)) (var 5) ⟶
        distanceBounded (ap2 G (var 0) (P (var 1 + succ (var 5) * var 3) (var 2) (var 3) (var 4)))
          (ap2 logF (var 0) (L (var 5) one))
          (num 2 * radius (var 1 + var 3) (var 2) * unit (var 0) + num 8 * var 5) (var 5 * unit (var 0))) :=
  closeUniv 6 (.impI (.impI (terminal_sample_error _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTerminalShiftError
