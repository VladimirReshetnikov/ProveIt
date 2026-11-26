import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedThreeSplit
import IPRADerivations.Analysis.Names.Rates.GaussianCompactModulusAlignedTime
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpAlignedFourSplit
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# The actual sharp grid with one contiguous tail from N/2 to top

Only aligned-time observations are needed for the finite split. The
original low and middle grids are unchanged; the third actual grid uses
the sum of the support-tail and exterior widths, without splitting at N.
All zero widths, including N=2, retain their actual empty sums. The
original Euler modulus supplies a separate unconditional specialization.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpAlignedThreeSplit

open_ipra
open GaussianBetaSharpPartition (lowWidth middleWidth supportTailWidth exteriorWidth halfPoint)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianCompactAlignedTime (alignedSamples)
open GaussianCompactAlignedSplit (quadrature_congr)
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tailWidth (k A R N : PTm n) : PTm n := supportTailWidth k A R N+exteriorWidth k A R N
def threePieces (F : PR 3) (s k A R N K x : PTm n) : PTm n :=
  qadd (qadd (quadrature F s (lowWidth k A R*K) one (lowWidth k A R) (etaDen k A R) x)
    (quadrature F s (middleWidth k A R N*K) (etaDen k A R) (middleWidth k A R N) (etaDen k A R) x))
    (quadrature F s (tailWidth k A R N*K) (halfPoint k A R N) (tailWidth k A R N) (etaDen k A R) x)
abbrev source (F : PR 3) (k A R N K x : PTm n) : Fm PTm n := GaussianBetaSharpAlignedFourSplit.source F k A R N K x

theorem tail_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    halfPoint k A R N+tailWidth k A R N ≐ etaDen k A R*top k A R := by
  have all := GaussianBetaSharpPartition.exact_partition k A R N h
  exact (add_assoc _ _ _).eqSymm.eqTrans ((congrAdd all.andE₂.andE₂.andE₁ (.eqRefl _)).eqTrans all.andE₂.andE₂.andE₂)

/-- Exact original parameter order: partition, common mesh, query, data. -/
theorem original_aligned_three_piece_split (F : PR 3) (k A R N K p x : PTm n)
    (h : Γ ⊢[PRAAx] source F k A R N K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (width k A R*K) one (width k A R) (etaDen k A R) x)
      (threePieces F p k A R N K x) (num 4*width k A R) (etaDen k A R*unit p) := by
  let C1 := lowWidth k A R
  let C2 := middleWidth k A R N
  let C3 := tailWidth k A R N
  let W := C1+C2+C3
  have w : Γ ⊢[PRAAx] W ≐ width k A R := GaussianBetaSharpAlignedFourSplit.total_width k A R N h.andE₁
  have aligned : Γ ⊢[PRAAx] alignedSamples F one W (etaDen k A R) x := by
    have direct := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (alignedSamples F one (var 0) (var 1) (var 2) : Fm PTm 3)
      ![width k A R,etaDen k A R,x] ![W,etaDen k A R,x]
      (fun i => by fin_cases i; exact w.eqSymm; exact .eqRefl _; exact .eqRefl _)
      (by simpa [one] using h.andE₂.andE₂)
    simpa [one] using direct
  have old := GaussianCompactAlignedThreeSplit.original_three_piece_split F p one C1 C2 C3 (etaDen k A R) K x
    (.andI (le_refl one) (.andI (eta_den_positive k A R) (.andI h.andE₂.andE₁ aligned)))
  have full := quadrature_congr (Γ := Γ) F (.eqRefl p) (congrMul w (.eqRefl K)) (.eqRefl one) w (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q2 := quadrature_congr (Γ := Γ) F (.eqRefl p) (.eqRefl (C2*K)) (GaussianBetaSharpPartition.exact_partition k A R N h.andE₁).andE₁
    (.eqRefl C2) (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q3 := quadrature_congr (Γ := Γ) F (.eqRefl p) (.eqRefl (C3*K)) (GaussianBetaSharpAlignedFourSplit.first_two_endpoint k A R N h.andE₁)
    (.eqRefl C3) (.eqRefl (etaDen k A R)) (.eqRefl x)
  exact distance_congr full (qadd_congr (qadd_congr (.eqRefl _) q2) q3) (congrMul (.eqRefl (num 4)) w) (.eqRefl _) old

theorem original_modulus_three_piece_split (F : PR 3) (k A R N K p L x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) (hK : Γ ⊢[PRAAx] le one K)
    (hm : Γ ⊢[PRAAx] sampledModulus F one (width k A R) (etaDen k A R) L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (width k A R*K) one (width k A R) (etaDen k A R) x)
      (threePieces F p k A R N K x) (num 4*width k A R) (etaDen k A R*unit p) :=
  original_aligned_three_piece_split F k A R N K p x
    (.andI h (.andI hK (GaussianCompactModulusAlignedTime.of_sampled_modulus F _ _ _ L x hm)))

theorem original_Euler_three_piece_split (k A R N K p z B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hp : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF p (width k A R*K) one (width k A R) (etaDen k A R) (GaussianEulerIntegrandName.fixedData z B))
      (threePieces GaussianEulerIntegrandName.evaluatorF p k A R N K (GaussianEulerIntegrandName.fixedData z B))
      (num 4*width k A R) (etaDen k A R*unit p) := by
  have interval : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B one (width k A R) (etaDen k A R) (top k A R) :=
    .andI (.andI h.andE₁ (.andI (eta_den_positive k A R) h.andE₂))
      (.andI (le_refl one) (le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A R).eqSymm (.eqRefl _) (le_refl _)))
  exact original_modulus_three_piece_split GaussianEulerIntegrandName.evaluatorF k A R N K p
    (GaussianEulerCompactModulus.lipschitz R (etaDen k A R) (top k A R)) (GaussianEulerIntegrandName.fixedData z B) hp hK
    (GaussianEulerCompactAdditivity.sampled_modulus z R B one (width k A R) (etaDen k A R) (top k A R) interval)

theorem actual_sharp_three_contiguous_grids_aligned_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source F (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) ⟶
      distanceBounded (quadrature F (var 5) (width (var 0) (var 1) (var 2)*var 4) one
        (width (var 0) (var 1) (var 2)) (etaDen (var 0) (var 1) (var 2)) (var 6))
        (threePieces F (var 5) (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))
        (num 4*width (var 0) (var 1) (var 2)) (etaDen (var 0) (var 1) (var 2)*unit (var 5))) :=
  closeUniv 7 (.impI (original_aligned_three_piece_split F _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_source_only_Euler_three_contiguous_grids_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaEulerCompactQuadrature.source (var 6) (var 2) (var 7) ⋏
      GaussianBetaSharpPartition.source (var 0) (var 1) (var 2) (var 3) ⋏ le one (var 4)) ⟶
      distanceBounded
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 5) (width (var 0) (var 1) (var 2)*var 4) one
          (width (var 0) (var 1) (var 2)) (etaDen (var 0) (var 1) (var 2)) (GaussianEulerIntegrandName.fixedData (var 6) (var 7)))
        (threePieces GaussianEulerIntegrandName.evaluatorF (var 5) (var 0) (var 1) (var 2) (var 3) (var 4) (GaussianEulerIntegrandName.fixedData (var 6) (var 7)))
        (num 4*width (var 0) (var 1) (var 2)) (etaDen (var 0) (var 1) (var 2)*unit (var 5))) :=
  closeUniv 8 (.impI (original_Euler_three_piece_split _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpAlignedThreeSplit
