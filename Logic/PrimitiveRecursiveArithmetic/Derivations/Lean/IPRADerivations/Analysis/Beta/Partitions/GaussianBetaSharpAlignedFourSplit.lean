import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactAlignedFourSplit
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpPartition
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpFourSplit

/-!
# The actual original eta-to-top grid split at one, N/2 and N

Only the actual aligned-time observation law is assumed. The old even
eta denominator gives exact integer numerator boundaries.
The four actual piece counts are their original numerical widths times
one shared mesh factor. The checked generic split allows all zero widths,
including the middle piece at N=2 and the exterior piece at N=top.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpAlignedFourSplit

open_ipra
open GaussianBetaSharpPartition (lowWidth middleWidth supportTailWidth exteriorWidth halfPoint)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCompactRiemannName (quadrature)
open GaussianCompactAlignedTime (alignedSamples)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev pieces (F : PR 3) (s k A R N K x : PTm n) : PTm n :=
  GaussianBetaSharpFourSplit.pieces F s k A R N K x

def source (F : PR 3) (k A R N K x : PTm n) : Fm PTm n :=
  GaussianBetaSharpPartition.source k A R N ⋏ (le one K ⋏ alignedSamples F one (width k A R) (etaDen k A R) x)

theorem total_width (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    GaussianCompactAlignedFourSplit.totalWidth (lowWidth k A R) (middleWidth k A R N) (supportTailWidth k A R N) (exteriorWidth k A R N) ≐ width k A R :=
  GaussianBetaSharpFourSplit.total_width k A R N h

alias first_two_endpoint := GaussianBetaSharpFourSplit.first_two_endpoint
alias first_three_endpoint := GaussianBetaSharpFourSplit.first_three_endpoint

/-- Original rational endpoints, actual piece grids and original evaluator. -/
theorem original_sharp_four_piece_split (F : PR 3) (s k A R N K x : PTm n)
    (h : Γ ⊢[PRAAx] source F k A R N K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s (width k A R*K) one (width k A R) (etaDen k A R) x)
      (pieces F s k A R N K x) (num 4*width k A R) (etaDen k A R*unit s) := by
  let C1 := lowWidth k A R
  let C2 := middleWidth k A R N
  let C3 := supportTailWidth k A R N
  let C4 := exteriorWidth k A R N
  let W := GaussianCompactAlignedFourSplit.totalWidth C1 C2 C3 C4
  have w := total_width k A R N h.andE₁
  have aligned : Γ ⊢[PRAAx] alignedSamples F one W (etaDen k A R) x := by
    have direct := Prf.eqSubst1
      (alignedSamples F (Syn.shift one) (var 0) (Syn.shift (etaDen k A R)) (Syn.shift x)) w.eqSymm
      (by simpa only [GaussianCompactAlignedTime.subst_alignedSamples,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        using h.andE₂.andE₂)
    simpa only [GaussianCompactAlignedTime.subst_alignedSamples,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using direct
  have input : Γ ⊢[PRAAx] GaussianCompactAlignedFourSplit.input F one C1 C2 C3 C4 (etaDen k A R) K x :=
    .andI (le_refl one) (.andI (eta_den_positive k A R) (.andI h.andE₂.andE₁ aligned))
  have old := GaussianCompactAlignedFourSplit.original_four_piece_split F s one C1 C2 C3 C4 (etaDen k A R) K x input
  exact GaussianBetaSharpFourSplit.transport_four_piece_split F s k A R N K x h.andE₁ old

/-- Public parameter order matches the original partition first, then
its shared mesh, observation precision and original evaluator data. -/
theorem original_aligned_four_piece_split (F : PR 3) (k A R N K p x : PTm n)
    (h : Γ ⊢[PRAAx] source F k A R N K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (width k A R*K) one (width k A R) (etaDen k A R) x)
      (GaussianBetaSharpFourSplit.pieces F p k A R N K x) (num 4*width k A R) (etaDen k A R*unit p) :=
  original_sharp_four_piece_split F p k A R N K x h

theorem original_aligned_sharp_four_actual_grids_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (quadrature F (var 0) (width (var 1) (var 2) (var 3)*var 5) one
        (width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)) (var 6))
        (pieces F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (num 4*width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)*unit (var 0))) :=
  closeUniv 7 (.impI (original_sharp_four_piece_split F _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpAlignedFourSplit
