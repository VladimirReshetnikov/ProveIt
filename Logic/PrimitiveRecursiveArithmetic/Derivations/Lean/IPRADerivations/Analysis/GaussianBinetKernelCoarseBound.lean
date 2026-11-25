import IPRADerivations.Analysis.GaussianBinetKernelCofinal

/-!
# Uniform bound on the original Binet kernel observations

The first row contributes at most 1/8, and the checked tail beginning
after it contributes at most 1/8. The bound also holds at the cofinal
kernel's actual sampling clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelCoarseBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelRows (inputData rowF rowBody rowData row_bound)
open GaussianBinetKernelTail (finiteF finiteData)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit_positive bounded_radius_mono)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "finite" => GaussianNamedFiniteSumFamily.finite rowF rowBody
local notation "observedBody" => GaussianNamedFiniteSumFamily.body rowF rowBody

private theorem first_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (finite p (succ zero) (inputData A B)) one (num 8) := by
  let x := inputData A B
  let y := pairT p x
  have entry := (GaussianNamedFiniteSumFamily.term_at (Γ := Γ) rowF rowBody zero p x).eqTrans
    (congrAp2 rowF (.eqRefl _) (GaussianBinetKernelRows.row_at zero A B))
  have hs : Γ ⊢[PRAAx] finite p (succ zero) x ≐
      GaussianRationalHorner.qadd qzero (ap2 rowF p (rowData zero A B)) :=
    (GaussianRationalFiniteSum.sum_succ observedBody zero y).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (GaussianRationalFiniteSum.sum_zero observedBody y) entry)
  have h8 := GaussianBinetKernelTailMajorant.eight_positive (Γ := Γ)
  have raw := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] num 8*(succ zero*succ zero) ≐ num 8)
    (row_bound p zero A B hB)
  have hz := (GaussianReconstructionRoots.distance_zero_iff (Γ := Γ) qzero zero one (le_refl one)).iffMp
    (GaussianRationalPowerDifference.distance_refl_zero qzero one (le_refl one))
  exact bound_congr hs.eqSymm (by ipra_ring) (one_mul _)
    (GaussianRationalReciprocal.bounded_sum _ _ zero one one (num 8) (le_refl one) h8 hz raw)

theorem finite_at (p N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (finite p N (inputData A B)) one (num 4) := by
  let x := inputData A B
  let y := pairT p x
  refine .orE (zero_or_succ N) ?_ ?_
  · have h : (N ≐ zero) :: Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
    have hf : (N ≐ zero) :: Γ ⊢[PRAAx] finite p N x ≐ qzero :=
      (GaussianRationalFiniteSum.sum_index_congr observedBody Prf.hyp0 (.eqRefl y)).eqTrans
        (GaussianRationalFiniteSum.sum_zero observedBody y)
    exact bound_congr hf.eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ (le_refl one) h (by ipra_le 1)
        ((GaussianReconstructionRoots.distance_zero_iff qzero zero one (le_refl one)).iffMp
          (GaussianRationalPowerDifference.distance_refl_zero qzero one (le_refl one))))
  · let r := pred N
    let Δ := (N ≐ succ r) :: Γ
    have e : Δ ⊢[PRAAx] succ zero+r ≐ N :=
      (by ipra_ring : Δ ⊢[PRAAx] succ zero+r ≐ succ r).eqTrans Prf.hyp0.eqSymm
    have h8 := GaussianBinetKernelTailMajorant.eight_positive (Γ := Δ)
    have gap : Δ ⊢[PRAAx] distanceBounded (finite p N x) (finite p (succ zero) x) one (num 8) :=
      distance_congr (GaussianRationalFiniteSum.sum_index_congr observedBody e (.eqRefl y))
        (.eqRefl _) (.eqRefl _) (by ipra_ring)
        (GaussianBinetKernelTail.finite_gap p (succ zero) r A B (zero_lt_succ zero) hB.wk)
    exact bounded_radius_mono _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ h8 h8) (by ipra_le 3)
      (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ h8 h8 gap (first_bound p A B hB.wk))

theorem named_finite_at (p N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 finiteF p (finiteData N A B)) one (num 4) :=
  bound_congr (GaussianNamedFiniteSumFamily.sample_at rowF rowBody p N (inputData A B)).eqSymm
    (.eqRefl _) (.eqRefl _) (finite_at (GaussianFastValueCut.exponent N p) N A B hB)

theorem cofinal_at (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 GaussianBinetKernelCofinal.nameF p (inputData A B)) one (num 4) :=
  bound_congr (GaussianBinetKernelCofinal.sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _)
    (named_finite_at (succ p) (GaussianBinetKernelCofinal.cutoff p) A B hB)

end LeanProofs.IPRA.Analysis.GaussianBinetKernelCoarseBound
