import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureSquarePartition

/-!
# Original uniform fine nodes inside an actual quadratic cell

Both the raw mapped time and every original target-grid node in its
polynomial block satisfy the original compact domain. Their numerical
values differ by at most one proved quadratic cell cap. This is a finite
geometry statement, with the same original time codes retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareGridDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalQuadratureSquarePartition
  (source lowerNumerator widthNumerator intervalDenominator fineCount cellCap cutValue cutData cutF cutGap)
open GaussianRationalQuadratureSquareCells (nodeNumerator denominator node)
open GaussianCompactRiemannName (grid value inside fraction_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def mappedTime (i N c d a C E : PTm n) : PTm n :=
  pairT (c*nodeNumerator i N a C*nodeNumerator i N a C) (denominator d E N)
def targetGrid (j N c d a C E : PTm n) : PTm n :=
  grid j (fineCount N c a C) (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E)

@[simp] theorem subst_mappedTime {m : ℕ} (σ : Fin n → PTm m) (i N c d a C E : PTm n) :
    Syn.subst σ (mappedTime i N c d a C E) = mappedTime (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ c)
      (Syn.subst σ d) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [mappedTime]
@[simp] theorem subst_targetGrid {m : ℕ} (σ : Fin n → PTm m) (j N c d a C E : PTm n) :
    Syn.subst σ (targetGrid j N c d a C E) = targetGrid (Syn.subst σ j) (Syn.subst σ N) (Syn.subst σ c)
      (Syn.subst σ d) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [targetGrid]

theorem target_denominator_positive (c d a C E N : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    le one (intervalDenominator d E) := positive_product _ _
      (positive_product _ _ hs.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂.andE₁) hs.andE₂.andE₂.andE₂.andE₂.andE₁

theorem mapped_value (i N c d a C E : PTm n) : Γ ⊢[PRAAx] value (mappedTime i N c d a C E) ≐ node i N c d a C E :=
  fraction_congr _ _ _ _ (fst_pair _ _) (snd_pair _ _)

theorem cutValue_monotone (i j N c a C : PTm n) (h : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    le (cutValue i N c a C) (cutValue j N c a C) := by
  unfold cutValue
  ipra_le (𝔞(c*C)*(2*𝔞(a)*𝔞(N)+𝔞(C)*(𝔞(i)+𝔞(j))))*sl h

theorem fine_index_bound (i j N c a C : PTm n) (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j (cutGap i N c a C)) : Γ ⊢[PRAAx]
    le (ap2 cutF i (cutData N c a C)+j) (fineCount N c a C) := by
  have order := GaussianPartitionedFiniteSum.cut_step (Γ := Γ) cutF (cutData N c a C) i (GaussianRationalQuadratureSquarePartition.increasing N c a C)
  have first : Γ ⊢[PRAAx] le (ap2 cutF i (cutData N c a C)+j) (ap2 cutF (succ i) (cutData N c a C)) :=
    le_congr (.eqRefl _) (eq_add_of_le order).eqSymm (add_le_add₂ (le_refl _) (le_of_lt hj))
  have last : Γ ⊢[PRAAx] le (ap2 cutF (succ i) (cutData N c a C)) (fineCount N c a C) :=
    le_congr (GaussianRationalQuadratureSquarePartition.cut_at (succ i) N c a C).eqSymm
      (by unfold cutValue fineCount widthNumerator; ipra_ring) (cutValue_monotone (succ i) N N c a C hi)
  exact le_trans first last

theorem target_inside (i j N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N)
    (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j (cutGap i N c a C)) : Γ ⊢[PRAAx]
    inside (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E)
      (targetGrid (ap2 cutF i (cutData N c a C)+j) N c d a C E) :=
  GaussianCompactRiemannName.grid_inside _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hs.andE₁ hs.andE₂.andE₁) hs.andE₂.andE₁)
    (target_denominator_positive c d a C E N hs) (GaussianRationalQuadratureSquarePartition.fine_count_positive c d a C E N hs)
    (fine_index_bound i j N c a C hi hj)

theorem mapped_inside (i N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    inside (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) (mappedTime i N c d a C E) := by
  have hN := hs.andE₂.andE₂.andE₂.andE₂.andE₂
  have hD := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  have lowNode : Γ ⊢[PRAAx] le (a*N) (nodeNumerator i N a C) := le_add_right _ _
  have highNode : Γ ⊢[PRAAx] le (nodeNumerator i N a C) ((a+C)*N) := by unfold nodeNumerator; ipra_le 𝔞(C)*sl hi
  have hn : Γ ⊢[PRAAx] le one (nodeNumerator i N a C) := le_trans (positive_product _ _ hs.andE₂.andE₁ hN) lowNode
  have numeratorPos := positive_product _ _ (positive_product _ _ hs.andE₁ hn) hn
  have lower : Γ ⊢[PRAAx] le (lowerNumerator c a*denominator d E N)
      (intervalDenominator d E*(c*nodeNumerator i N a C*nodeNumerator i N a C)) :=
    le_congr (by unfold lowerNumerator denominator intervalDenominator; ipra_ring)
      (by ipra_ring) (mul_le_mul_right (c*intervalDenominator d E) (sq_le_sq lowNode))
  have upper : Γ ⊢[PRAAx] le (intervalDenominator d E*(c*nodeNumerator i N a C*nodeNumerator i N a C))
      ((lowerNumerator c a+widthNumerator c a C)*denominator d E N) :=
    le_congr (by ipra_ring) (by unfold lowerNumerator widthNumerator denominator intervalDenominator; ipra_ring)
      (mul_le_mul_right (c*intervalDenominator d E) (sq_le_sq highNode))
  exact .andI (le_congr (.eqRefl _) (fst_pair _ _).eqSymm numeratorPos)
    (.andI (le_congr (.eqRefl _) (snd_pair _ _).eqSymm hD)
      (.andI (le_congr (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm lower)
        (le_congr (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm upper)))

theorem fine_value (j N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    value (targetGrid j N c d a C E) ≐ fraction (lowerNumerator c a*N*N+j) (denominator d E N) := by
  have hW := GaussianRationalQuadratureSquarePartition.width_positive c d a C E N hs
  have hD := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  exact (GaussianCompactRiemannName.value_grid _ _ _ _ _).eqTrans
    ((fraction_congr _ _ _ _ (by unfold fineCount; ipra_ring)
      (by unfold intervalDenominator fineCount denominator; ipra_ring)).eqTrans
        (GaussianCompactRiemannSplit.fraction_cancel _ _ _ hW hD))

theorem fine_difference (i j N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (value (targetGrid (ap2 cutF i (cutData N c a C)+j) N c d a C E))
      (value (targetGrid (ap2 cutF i (cutData N c a C)) N c d a C E)) ≐ fraction j (denominator d E N) := by
  let b := lowerNumerator c a*N*N+ap2 cutF i (cutData N c a C)
  let D := denominator d E N
  have hD := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  have first : Γ ⊢[PRAAx] value (targetGrid (ap2 cutF i (cutData N c a C)+j) N c d a C E) ≐ fraction (b+j) D :=
    (fine_value _ N c d a C E hs).eqTrans (fraction_congr _ _ _ _ (by dsimp only [b]; ipra_ring) (.eqRefl _))
  have second := fine_value (ap2 cutF i (cutData N c a C)) N c d a C E hs
  have split := GaussianRationalQuadratureSquareCells.fraction_add_same b j D hD
  exact (qsub_congr first second).eqTrans ((qsub_congr split.eqSymm (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hD)))

/-- Source-only distance between the genuine fine-node value and the
original mapped-node value, preserving their different raw encodings. -/
theorem original_block_distance (i j N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N)
    (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j (cutGap i N c a C)) : Γ ⊢[PRAAx]
    distanceBounded (value (targetGrid (ap2 cutF i (cutData N c a C)+j) N c d a C E)) (value (mappedTime i N c d a C E))
      (cellCap c a C) (intervalDenominator d E*N) := by
  have hD := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  have hN := hs.andE₂.andE₂.andE₂.andE₂.andE₂
  have newDen := positive_product _ _ (target_denominator_positive c d a C E N hs) hN
  have jBound := le_trans (le_of_lt hj) (GaussianRationalQuadratureSquarePartition.cut_gap_bound i N c a C hi)
  have raw := GaussianRationalReciprocal.bound_congr (fine_difference i j N c d a C E hs).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point j (denominator d E N) hD).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded j (denominator d E N) hD))
  have enlarged := distance_radius_mono _ _ _ _ (cellCap c a C) (intervalDenominator d E*N) hD newDen
    (le_congr (.eqRefl _) (by unfold denominator intervalDenominator; ipra_ring) (mul_le_mul_right (intervalDenominator d E*N) jBound)) raw
  exact distance_congr (.eqRefl _)
    ((GaussianRationalQuadratureSquarePartition.point_at_cut i N c d a C E hs).eqTrans (mapped_value i N c d a C E).eqSymm) (.eqRefl _) (.eqRefl _) enlarged

theorem actual_original_square_block_geometry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 2) ⋏
      (lt (var 0) (var 2) ⋏ lt (var 1) (cutGap (var 0) (var 2) (var 3) (var 5) (var 6)))) ⟶
      distanceBounded (value (targetGrid (ap2 cutF (var 0) (cutData (var 2) (var 3) (var 5) (var 6))+var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (value (mappedTime (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (cellCap (var 3) (var 5) (var 6)) (intervalDenominator (var 4) (var 7)*var 2)) :=
  closeUniv 8 (.impI (original_block_distance _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareGridDistance
