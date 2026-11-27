import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.Compact.GaussianEulerUnitKernelCompactName
import IPRADerivations.Analysis.Integration.Quadrature.GaussianAffinePanelDisplacement
import IPRADerivations.Analysis.Integration.Partitions.GaussianWeightedPanelRowDistance

/-!
# Source-only endpoint continuity of actual ordinary unit-kernel panels

The two original affine quadratures retain one common positive count and
independent kernel observation queries. Genuine endpoint displacement
bounds both matched times and the actual weights. Weighted rows preserve
each observation allowance exactly when the original finite sum cancels
its common count. Zero physical widths are admitted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelContinuity

open_ipra
open GaussianEulerUnitKernelCompactName (evaluatorF fixedData)
open GaussianEulerUnitKernelCompactRate (lipschitz majorant)
open GaussianCompactRiemannName (sampleBody sampleData grid quadrature)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalRiemannRefinement (weight termsDistance sum_distance)
open GaussianAffinePanelDisplacement (endpointSource)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C b D M G A : PTm n) : Fm PTm n :=
  GaussianEulerUnitKernelCompactName.source z R B a C M G ⋏
    (GaussianEulerUnitKernelCompactName.source z R B b D M G ⋏ endpointSource a C b D A)
def leading (R G A : PTm n) : PTm n := (lipschitz R G+two*majorant R G)*A

ipra_subst source
ipra_subst leading

private theorem native_source_congr {z R B a b c d G : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d)
    (h : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.source z R B a b G) :
    Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.source z R B c d G := by
  have first : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.source z R B c b G := by
    simpa using Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
      (GaussianEulerUnitKernelCompactRate.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0) (Syn.shift b) (Syn.shift G)) ha (by simpa using h)
  simpa using Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
    (GaussianEulerUnitKernelCompactRate.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift c) (var 0) (Syn.shift G)) hb (by simpa using first)

theorem original_grid_source (i H z R B a C M G : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactName.source z R B a C M G)
    (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] le i H) : Γ ⊢[PRAAx]
    GaussianEulerUnitKernelCompactRate.source z R B (a*H+C*i) (M*H) G := by
  have inside := GaussianCompactRiemannName.grid_inside i H a C M
    (GaussianEulerUnitKernelCompactName.start_positive z R B a C M G hs) hs.andE₂.andE₁ hH hi
  exact native_source_congr (fst_pair _ _) (snd_pair _ _)
    (GaussianEulerUnitKernelCompactName.inside_source z R B a C M G (grid i H a C M) hs inside)

private theorem row_at (i p H z B a C M : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i (sampleData p H a C M (fixedData z B)) ≐
      ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data z B (a*H+C*i) (M*H)) :=
  (GaussianCompactRiemannName.sample_body_at evaluatorF i p H a C M (fixedData z B)).eqTrans
    (GaussianEulerUnitKernelCompactName.sample_at p z B _ _)

private theorem weighted_row_at (i p H z B a C M : PTm n) : Γ ⊢[PRAAx]
    inst2 (multiplyBody (sampleBody evaluatorF)) i
      (pairT (weight C M H) (sampleData p H a C M (fixedData z B))) ≐
      qmul (ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data z B (a*H+C*i) (M*H)))
        (weight C M H) :=
  (multiply_body_at (sampleBody evaluatorF) (weight C M H) i _).eqTrans
    ((qmul_congr (.eqRefl _) (row_at i p H z B a C M)).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))

theorem original_weighted_row_distance (i p q H z R B a C b D M G A : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C b D M G A) (hH : Γ ⊢[PRAAx] le one H)
    (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (multiplyBody (sampleBody evaluatorF)) i (pairT (weight C M H) (sampleData p H a C M (fixedData z B))))
      (inst2 (multiplyBody (sampleBody evaluatorF)) i (pairT (weight D M H) (sampleData q H b D M (fixedData z B))))
      (GaussianWeightedPanelRowDistance.numerator (lipschitz R G) (majorant R G) A M (unit p) (unit q))
      (GaussianWeightedPanelRowDistance.denominator H M (unit p) (unit q)) := by
  have hM := hs.andE₁.andE₂.andE₁
  have hMH := positive_product _ _ hM hH
  have left := original_grid_source i H z R B a C M G hs.andE₁ hH (le_of_lt hi)
  have right := original_grid_source i H z R B b D M G hs.andE₂.andE₁ hH (le_of_lt hi)
  have geo := GaussianAffinePanelDisplacement.grid_fraction_distance i H a C b D M A hM hH (le_of_lt hi) hs.andE₂.andE₂
  have near := GaussianEulerUnitKernelCompactRate.original_observations p q z R B (a*H+C*i) (M*H) (b*H+D*i) (M*H) G A M
    (.andI left (.andI right (.andI hM geo)))
  have width : Γ ⊢[PRAAx] distanceBounded (weight C M H) (weight D M H) (two*A) (M*H) :=
    GaussianAffinePanelDisplacement.width_distance a C b D (M*H) A hMH hs.andE₂.andE₂
  have hC : Γ ⊢[PRAAx] le C M := le_trans (le_add_left C a)
    (GaussianEulerUnitKernelCompactName.right_endpoint_le_one z R B a C M G hs.andE₁)
  have leftBound : Γ ⊢[PRAAx] bounded (weight C M H) one H :=
    bounded_radius_mono _ _ _ _ _ hMH hH
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right H hC))
      (GaussianRationalRiemannRefinement.weight_bound C M H hM hH)
  have pointBound := GaussianEulerUnitKernelCompactRate.original_bound q z R B _ _ G right
  have raw := GaussianWeightedPanelRowDistance.original_row_distance _ _ _ _ (lipschitz R G) (majorant R G) A M H
    (unit p) (unit q) hM hH (unit_positive p) (unit_positive q) near leftBound pointBound width
  exact distance_congr (weighted_row_at i p H z B a C M).eqSymm (weighted_row_at i q H z B b D M).eqSymm
    (.eqRefl _) (.eqRefl _) raw

theorem original_weighted_rows (p q H z R B a C b D M G A : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C b D M G A) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    termsDistance (multiplyBody (sampleBody evaluatorF)) (multiplyBody (sampleBody evaluatorF)) H
      (pairT (weight C M H) (sampleData p H a C M (fixedData z B)))
      (pairT (weight D M H) (sampleData q H b D M (fixedData z B)))
      (GaussianWeightedPanelRowDistance.numerator (lipschitz R G) (majorant R G) A M (unit p) (unit q))
      (GaussianWeightedPanelRowDistance.denominator H M (unit p) (unit q)) := by
  let s (u : PTm n) := Syn.shift u
  have hss : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) (s a) (s C) (s b) (s D) (s M) (s G) (s A) := by
    simpa [Fm.shift,Syn.shift,s] using hs.shift
  have hh : Γ.map Fm.shift ⊢[PRAAx] le one (s H) := by simpa [Fm.shift,Syn.shift,s] using hH.shift
  refine .allI (.impI ?_)
  simpa only [termsDistance,GaussianRationalRiemannRefinement.subst_weight,subst_pairT,GaussianCompactRiemannName.subst_sampleData,
    GaussianEulerUnitKernelCompactName.subst_fixedData,GaussianEulerUnitKernelCompactRate.subst_lipschitz,
    GaussianEulerUnitKernelCompactRate.subst_majorant,GaussianWeightedPanelRowDistance.subst_numerator,
    GaussianWeightedPanelRowDistance.subst_denominator,GaussianCoefficientNameBounds.subst_unit,Syn.shift,s] using
    original_weighted_row_distance (var 0) (s p) (s q) (s H) (s z) (s R) (s B) (s a) (s C) (s b) (s D) (s M) (s G) (s A)
      hss.wk hh.wk Prf.hyp0

theorem original_same_count_bound (p q H z R B a C b D M G A : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C b D M G A) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p H a C M (fixedData z B))
      (quadrature evaluatorF q H b D M (fixedData z B))
      (rateNumerator (leading R G A) M p q) (rateDenominator M p q) := by
  have hM := hs.andE₁.andE₂.andE₁
  have hQ := positive_product _ _ (positive_product _ _ hM (unit_positive (Γ := Γ) p)) (unit_positive q)
  have hD := positive_product _ _ hH hQ
  have rows := original_weighted_rows p q H z R B a C b D M G A hs hH
  have raw := sum_distance _ _ _ _ _ _ _ hD rows
  have actual := distance_congr (sum_multiply (sampleBody evaluatorF) (weight C M H) H _)
    (sum_multiply (sampleBody evaluatorF) (weight D M H) H _) (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ hD hQ
    (le_of_eq_add (d := zero) (by
      simp only [GaussianWeightedPanelRowDistance.numerator,rateNumerator,rateDenominator,leading]
      ipra_ring)) actual


theorem actual_original_unit_kernel_panel_quadrature_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ le one (var 2)) ⟶
      distanceBounded
        (quadrature evaluatorF (var 0) (var 2) (var 6) (var 7) (var 10) (fixedData (var 3) (var 5)))
        (quadrature evaluatorF (var 1) (var 2) (var 8) (var 9) (var 10) (fixedData (var 3) (var 5)))
        (rateNumerator (leading (var 4) (var 11) (var 12)) (var 10) (var 0) (var 1))
        (rateDenominator (var 10) (var 0) (var 1))) :=
  closeUniv 13 (.impI (original_same_count_bound _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelContinuity
