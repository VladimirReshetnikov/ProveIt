import IPRADerivations.Analysis.GaussianLogGammaEulerCofinal
import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithmRescale
import IPRADerivations.Analysis.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.GaussianGammaCompactCutoffAlignment

/-!
# Transport the original log-Gamma name across a common denominator

Every shifted logarithm row has the same value after rescaling all
three rational coordinates. The finite heads therefore agree, and the
same positive cutoff can be used to compare both original cofinal names.
-/

set_option autoImplicit false
set_option maxHeartbeats 180000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianLogGammaEulerCofinal (canonicalData canonical_regular cutoff cutoff_positive late_cutoff_distance sample_at)
open GaussianLogGammaEulerHead (argument productF rowBody rowData shifted_source sum_regular)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_to_diagonal cross_trans)
open GaussianNameRingLaws (equivalent_of_envelope negativeF negativeData negative_fast negative_equivalent)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Products (fact)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "rowF" => GaussianRightHalfPlaneLogarithm.nameF
local notation "rowAt" => GaussianRightHalfPlaneLogarithm.data
local notation "headF" => GaussianLogGammaEulerHead.nameF
local notation "headData" => GaussianLogGammaEulerHead.data
local notation "headSumF" => GaussianLogGammaEulerHead.sumF
local notation "headSumData" => GaussianLogGammaEulerHead.sumData
local notation "normalizedF" => GaussianLogGammaEulerNormalizedHead.nameF
local notation "cofinalF" => GaussianLogGammaEulerCofinal.nameF
local notation "radius" => GaussianLogGammaEulerResidualRadius.radius

private theorem rescaled_source (A D neg k d : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (hd : Γ ⊢[PRAAx] k*D ≐ d) : Γ ⊢[PRAAx] source (k*A) d neg :=
  .andI (.andI (positive_product k A hk h.andE₁.andE₁) h.andE₁.andE₂)
    (le_congr (.eqRefl _) hd (positive_product k D hk h.andE₂))

private theorem rescaled_row (A B D neg k d i : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (hd : Γ ⊢[PRAAx] k*D ≐ d) : Γ ⊢[PRAAx]
    crossEquivalent rowF rowF (inst2 rowBody i (rowData (k*A) (k*B) d neg))
      (inst2 rowBody i (rowData A B D neg)) := by
  have ea : Γ ⊢[PRAAx] k*(A+i*D) ≐ k*A+i*d :=
    (show Γ ⊢[PRAAx] k*(A+i*D) ≐ k*A+i*(k*D) by ipra_ring).eqTrans
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) hd))
  have link : Γ ⊢[PRAAx] rowAt (k*(A+i*D)) (k*B) (k*D) neg ≐ rowAt (k*A+i*d) (k*B) d neg := by
    simpa only [GaussianRightHalfPlaneLogarithm.subst_data, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rowAt (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![k*(A+i*D),k*B,k*D,neg]) (σ' := ![k*A+i*d,k*B,d,neg])
        (fun j => by fin_cases j; exact ea; exact .eqRefl _; exact hd; exact .eqRefl _)
  exact cross_data_congr rowF rowF _ _ _ _
    (link.eqTrans (GaussianLogGammaEulerHead.row_at i (k*A) (k*B) d neg).eqSymm)
    (GaussianLogGammaEulerHead.row_at i A B D neg).eqSymm
    (GaussianRightHalfPlaneLogarithmRescale.rescale (A+i*D) B D neg k (shifted_source i A D neg h) hk)

private theorem sum_rescale (A B D neg k d N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (hd : Γ ⊢[PRAAx] k*D ≐ d) : Γ ⊢[PRAAx]
    crossEquivalent headSumF headSumF (headSumData (k*A) (k*B) d neg N) (headSumData A B D neg N) := by
  apply family_sum_cross rowF rowF rowBody rowBody (succ N) (rowData (k*A) (k*B) d neg) (rowData A B D neg)
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (s (succ N)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have hks : Δ ⊢[PRAAx] le one (s k) := by simpa [Δ,s,Fm.shift,Syn.shift] using hk.shift.wk
  have hds : Δ ⊢[PRAAx] (s k)*(s D) ≐ s d := by simpa [Δ,s,Fm.shift,Syn.shift] using hd.shift.wk
  simpa only [Δ,s,Syn.shift,GaussianLogGammaEulerHead.subst_rowData,PTm.subst_mul] using
    rescaled_row (s A) (s B) (s D) (s neg) (s k) (s d) (var 0) hs hks hds

theorem finite_rescale (A B D neg k d N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (hd : Γ ⊢[PRAAx] k*D ≐ d) (hN : Γ ⊢[PRAAx] le one N)
    (hpoint : Γ ⊢[PRAAx] argument (k*A) (k*B) d neg ≐ argument A B D neg) : Γ ⊢[PRAAx]
    crossEquivalent headF headF (headData (k*A) (k*B) d neg N) (headData A B D neg N) := by
  let x := argument (k*A) (k*B) d neg
  let y := argument A B D neg
  let z := L N one
  let c := L (fact N) one
  let u := headSumData (k*A) (k*B) d neg N
  let v := headSumData A B D neg N
  have hs := rescaled_source A D neg k d h hk hd
  have hn := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have hf := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (fact N) one
    (.andI (GammaEulerMesh.factorial_positive N) (le_refl one))
  have he : Γ ⊢[PRAAx] crossEquivalent constantF constantF x y :=
    cross_data_congr _ _ _ _ _ _ (.eqRefl _) hpoint (cross_refl constantF x (constant_regular x))
  have hp := multiply_cross constantF constantF logF logF x y z z
    (constant_regular x) (constant_regular y) hn hn he (cross_refl logF z hn)
  have hpx := multiply_fast constantF logF x z (constant_regular x) hn
  have hpy := multiply_fast constantF logF y z (constant_regular y) hn
  have hu := sum_regular (k*A) (k*B) d neg N hs
  have hv := sum_regular A B D neg N h
  have hm := negative_equivalent headSumF headSumF u v hu hv
    (cross_to_diagonal _ _ _ _ (sum_rescale A B D neg k d N h hk hd))
  have front := add_cross logF logF productF productF c c _ _ hf hf hpx hpy (cross_refl logF c hf) hp
  exact add_cross (addF logF productF) (addF logF productF) (negativeF headSumF) (negativeF headSumF)
    _ _ (negativeData u) (negativeData v) (add_fast _ _ _ _ hf hpx) (add_fast _ _ _ _ hf hpy)
    (negative_fast _ _ hu) (negative_fast _ _ hv) front hm

private theorem cofinal_diagonal (p A B D neg k d : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (hd : Γ ⊢[PRAAx] k*D ≐ d)
    (hpoint : Γ ⊢[PRAAx] argument (k*A) (k*B) d neg ≐ argument A B D neg) : Γ ⊢[PRAAx]
    distanceBounded (ap2 cofinalF p (canonicalData (k*A) (k*B) d neg)) (ap2 cofinalF p (canonicalData A B D neg))
      (num 6) (unit p) := by
  let R := radius (k*A) (k*B)
  let S := radius A B
  let N := cutoff R p + cutoff S p
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have hD := positive_product U U hU hU
  have hs := rescaled_source A D neg k d h hk hd
  have hN := le_trans (cutoff_positive (Γ := Γ) R p) (le_add_right _ _ : Γ ⊢[PRAAx] le (cutoff R p) N)
  have left := late_cutoff_distance p p (k*A) (k*B) d neg R N
    (GaussianLogGammaEulerResidualRadius.source_of_right_half_plane (k*A) (k*B) d neg hs) (le_add_right _ _)
  have right := late_cutoff_distance p p A B D neg S N
    (GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A B D neg h) (le_add_left _ _)
  have leftHead := GaussianLogGammaEulerNormalizedHead.equivalent (k*A) (k*B) d neg N hs hN
  have rightHead := GaussianLogGammaEulerNormalizedHead.equivalent A B D neg N h hN
  have common := cross_trans normalizedF headF normalizedF _ _ _ (cross_symm _ _ _ _ leftHead)
    (cross_trans headF headF normalizedF _ _ _ (finite_rescale A B D neg k d N h hk hd hN hpoint) rightHead)
  have middle := cross_at normalizedF normalizedF _ _ p p common
  have gap := distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD left middle)
    (distance_symmetric _ _ _ _ hD right)
  have result := distance_radius_mono _ _ _ _ (num 6) U hD hU
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) gap
  exact distance_congr (sample_at p (k*A) (k*B) d neg R).eqSymm (sample_at p A B D neg S).eqSymm
    (.eqRefl _) (.eqRefl _) result

theorem canonical_rescale (A B D neg k d : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) (hd : Γ ⊢[PRAAx] k*D ≐ d)
    (hpoint : Γ ⊢[PRAAx] argument (k*A) (k*B) d neg ≐ argument A B D neg) : Γ ⊢[PRAAx]
    crossEquivalent cofinalF cofinalF (canonicalData (k*A) (k*B) d neg) (canonicalData A B D neg) := by
  apply equivalent_of_envelope _ _ _ _ (num 6)
    (canonical_regular _ _ _ _ (rescaled_source A D neg k d h hk hd)) (canonical_regular _ _ _ _ h)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let s (v : PTm n) := Syn.shift v
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  have ks : Δ ⊢[PRAAx] le one (s k) := by simpa [Δ,s,Fm.shift,Syn.shift] using hk.shift
  have ds : Δ ⊢[PRAAx] (s k)*(s D) ≐ s d := by simpa [Δ,s,Fm.shift,Syn.shift] using hd.shift
  have ps : Δ ⊢[PRAAx] argument ((s k)*(s A)) ((s k)*(s B)) (s d) (s neg) ≐ argument (s A) (s B) (s D) (s neg) := by
    simpa [Δ,s,Fm.shift,Syn.shift,argument,ZT.subst,ZT.ofNat] using hpoint.shift
  simpa only [Δ,s,Syn.shift,canonicalData,GaussianLogGammaEulerCofinal.subst_data,
    GaussianLogGammaEulerResidualRadius.subst_radius,PTm.subst_mul,PTm.subst_num] using
    cofinal_diagonal (var 0) (s A) (s B) (s D) (s neg) (s k) (s d) hs ks ds ps

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRescale
