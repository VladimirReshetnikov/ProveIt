import IPRADerivations.Analysis.Beta.GaussianBetaSharpAlignedThreeSplit
import IPRADerivations.Analysis.Beta.GaussianBetaMiddleDyadicBudget
import IPRADerivations.Analysis.Beta.GaussianBetaContiguousUpperTail
import IPRADerivations.Analysis.Beta.GaussianBetaZeroExtendedGrid

/-!
# Actual sharp three-piece grids aligned with their middle and tail bounds

The middle starts at the numerator E over E, hence at rational time one.
Its zero extension is literally the original supported beta grid. The
contiguous tail width is the exact monus width used by the checked tail
API. No denominator rescaling or query change is made. A threshold on
the common mesh factor handles positive middle widths; an actual empty
sum handles N=2 without an impossible positive-count premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpPieceAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpPartition (lowWidth middleWidth halfPoint)
open GaussianBetaSharpAlignedThreeSplit (tailWidth threePieces)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianCompactRiemannName (quadrature)
open GaussianCompactAlignedSplit (quadrature_congr)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def low (F : PR 3) (p k A R _N K x : PTm n) : PTm n :=
  quadrature F p (lowWidth k A R*K) one (lowWidth k A R) (etaDen k A R) x
def middle (F : PR 3) (p k A R N K x : PTm n) : PTm n :=
  quadrature F p (middleWidth k A R N*K) (etaDen k A R) (middleWidth k A R N) (etaDen k A R) x
def tail (F : PR 3) (p k A R N K x : PTm n) : PTm n :=
  quadrature F p (tailWidth k A R N*K) (halfPoint k A R N) (tailWidth k A R N) (etaDen k A R) x

theorem three_pieces_at (F : PR 3) (p k A R N K x : PTm n) : Γ ⊢[PRAAx]
    threePieces F p k A R N K x ≐ qadd (qadd (low F p k A R N K x) (middle F p k A R N K x)) (tail F p k A R N K x) := .eqRefl _

theorem middle_supported (p k A R N K z B : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    middle GaussianBetaZeroExtension.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N) ≐
      middle GaussianBetaKernelGridComparison.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N) := by
  have endpoint := (GaussianBetaSharpPartition.exact_partition k A R N h).andE₂.andE₁
  have within := (GaussianBetaSharpPartition.half_boundary_order k A R N h.andE₁ h.andE₂.andE₁).andE₂
  exact GaussianBetaZeroExtendedGrid.same_supported_grid p (middleWidth k A R N*K) (etaDen k A R)
    (middleWidth k A R N) (etaDen k A R) z B N (le_congr endpoint.eqSymm (.eqRefl _) within)

theorem low_supported (p k A R N K z B : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    low GaussianBetaZeroExtension.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N) ≐
      low GaussianBetaKernelGridComparison.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N) := by
  have positive := le_trans (le_succ_self one) h.andE₂.andE₁
  have within : Γ ⊢[PRAAx] le (etaDen k A R) (etaDen k A R*N) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (etaDen k A R) positive)
  exact GaussianBetaZeroExtendedGrid.same_supported_grid p (lowWidth k A R*K) one (lowWidth k A R) (etaDen k A R) z B N
    (le_congr (GaussianBetaSharpPartition.exact_partition k A R N h).andE₁.eqSymm (.eqRefl _) within)

theorem doubled_half_point (k A R N : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    two*halfPoint k A R N ≐ etaDen k A R*N := by
  have even := natEq (GaussianBetaSharpPartition.even_denominator (Γ := Γ) k A R hA)
  apply deriveNat
  unfold halfPoint
  ipra_simps
  rw [even]
  ring

theorem middle_source (z R B k A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hp : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    GaussianBetaMiddleDyadicBudget.source z R B (middleWidth k A R N) (etaDen k A R) N := by
  have double := (congrMul (.eqRefl two) (GaussianBetaSharpPartition.exact_partition k A R N hp).andE₂.andE₁).eqTrans
    (doubled_half_point k A R N hp.andE₁)
  exact .andI h (.andI (eta_den_positive k A R) (.andI (le_trans (le_succ_self one) hp.andE₂.andE₁)
    (le_congr double.eqSymm (.eqRefl _) (le_refl _))))

/-- The common mesh threshold is sufficient also at the actual zero
middle width, where no positive width-scaled count can be asserted. -/
theorem original_middle_bound (p v j w k A R N K z B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hp : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N)
    (hK : Γ ⊢[PRAAx] le (GaussianBetaMiddleDyadicBudget.minimumMesh j (middleWidth k A R N) R) K)
    (hw : Γ ⊢[PRAAx] le (GaussianBetaMiddleDyadicBudget.minimumAuxiliary j (middleWidth k A R N) N R) w) : Γ ⊢[PRAAx]
    distanceBounded
      (middle GaussianBetaZeroExtension.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (middle GaussianEulerIntegrandName.evaluatorF v k A R N K (GaussianEulerIntegrandName.fixedData z B))
      (GaussianBetaMiddleDyadicBudget.numerator p v j R (middleWidth k A R N) (etaDen k A R) N)
      (GaussianBetaMiddleDyadicBudget.denominator p v j (etaDen k A R) N) := by
  let C := middleWidth k A R N
  let E := etaDen k A R
  have hn := le_trans (le_succ_self one) hp.andE₂.andE₁
  have he := eta_den_positive (Γ := Γ) k A R
  have hd := GaussianBetaMiddleDyadicBudget.denominator_positive (Γ := Γ) p v j E N he hn
  refine .orE (zero_or_succ C) ?_ ?_
  · have beta := (quadrature_congr (Γ := (C ≐ zero)::Γ) GaussianBetaZeroExtension.evaluatorF (.eqRefl p)
      ((congrMul Prf.hyp0 (.eqRefl K)).eqTrans (zero_mul K)) (.eqRefl E) Prf.hyp0 (.eqRefl E)
      (.eqRefl (GaussianBetaKernelGridComparison.sampleDataBeta z B N))).eqTrans
        (GaussianCompactAlignedSplit.quadrature_empty GaussianBetaZeroExtension.evaluatorF p E zero E _)
    have euler := (quadrature_congr (Γ := (C ≐ zero)::Γ) GaussianEulerIntegrandName.evaluatorF (.eqRefl v)
      ((congrMul Prf.hyp0 (.eqRefl K)).eqTrans (zero_mul K)) (.eqRefl E) Prf.hyp0 (.eqRefl E)
      (.eqRefl (GaussianEulerIntegrandName.fixedData z B))).eqTrans
        (GaussianCompactAlignedSplit.quadrature_empty GaussianEulerIntegrandName.evaluatorF v E zero E _)
    exact distance_congr beta.eqSymm euler.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianCompactAlignedSplit.distance_of_identity _ _ _ _ hd.wk (.eqRefl (qzero : PTm n)))
  · have hc : (C ≐ succ (pred C))::Γ ⊢[PRAAx] le one C :=
      le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred C))
    have growth : (C ≐ succ (pred C))::Γ ⊢[PRAAx] le K (C*K) :=
      le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right K hc)
    have old := GaussianBetaMiddleDyadicBudget.original_middle_dyadic_bound p v j w z R B C E N (C*K)
      (middle_source z R B k A N h.wk hp.wk) (le_trans hK.wk growth) hw.wk
    exact distance_congr (middle_supported p k A R N K z B hp.wk).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) old

theorem tail_width_alignment (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    tailWidth k A R N ≐ GaussianBetaContiguousUpperTail.width k A R N (top k A R) := by
  have mine := natEq (GaussianBetaSharpAlignedThreeSplit.tail_endpoint (Γ := Γ) k A R N h)
  have other := natEq (GaussianBetaContiguousUpperTail.geometry k A R N (top k A R) h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂).andE₂.andE₂.andE₂
  apply deriveNat
  dsimp only [GaussianBetaContiguousUpperTail.start] at other
  ipra_simps
  linear_combination mine-other

theorem tail_beta_alignment (p k A R N K z B : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    tail GaussianBetaZeroExtension.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N) ≐
      GaussianBetaContiguousUpperTail.beta p k A K z R B N (top k A R) :=
  quadrature_congr GaussianBetaZeroExtension.evaluatorF (.eqRefl p) (congrMul (tail_width_alignment k A R N h) (.eqRefl K))
    (.eqRefl (halfPoint k A R N)) (tail_width_alignment k A R N h) (.eqRefl (etaDen k A R)) (.eqRefl _)

theorem tail_euler_alignment (p k A R N K z B : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    tail GaussianEulerIntegrandName.evaluatorF p k A R N K (GaussianEulerIntegrandName.fixedData z B) ≐
      GaussianBetaContiguousUpperTail.euler p k A K z R B N (top k A R) :=
  quadrature_congr GaussianEulerIntegrandName.evaluatorF (.eqRefl p) (congrMul (tail_width_alignment k A R N h) (.eqRefl K))
    (.eqRefl (halfPoint k A R N)) (tail_width_alignment k A R N h) (.eqRefl (etaDen k A R)) (.eqRefl _)

theorem original_tail_bound (p q k A R N K z B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hp : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded
      (tail GaussianBetaZeroExtension.evaluatorF p k A R N K (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (tail GaussianEulerIntegrandName.evaluatorF p k A R N K (GaussianEulerIntegrandName.fixedData z B))
      (GaussianBetaContiguousUpperTail.numerator p q k A R N (top k A R) K
        (GaussianWeightedHalfDecayEndpoint.coefficient R*GaussianBetaContiguousUpperTail.sampleNumerator q N) (GaussianBetaContiguousUpperTail.sampleDenominator q N))
      (GaussianBetaContiguousUpperTail.denominator p q k A R N (top k A R) K (GaussianBetaContiguousUpperTail.sampleDenominator q N)) :=
  distance_congr (tail_beta_alignment p k A R N K z B hp).eqSymm (tail_euler_alignment p k A R N K z B hp).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBetaContiguousUpperTail.original_grid p q k A K z R B N (top k A R)
      (.andI h (.andI hp.andE₁ (.andI hp.andE₂.andE₁ (.andI hp.andE₂.andE₂ hK)))))

theorem actual_sharp_contiguous_tail_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBetaSharpPartition.source (var 0) (var 1) (var 2) (var 3) ⟶
      tailWidth (var 0) (var 1) (var 2) (var 3) ≐ GaussianBetaContiguousUpperTail.width (var 0) (var 1) (var 2) (var 3) (top (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (tail_width_alignment _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpPieceAlignment
