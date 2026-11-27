import IPRADerivations.Analysis.Names.Rates.RightHalfPlane.GaussianRightHalfPlaneArgumentChartContinuity
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianRightHalfPlaneArgumentIncrementGeometry
import IPRADerivations.Analysis.RationalArithmetic.Complex.Arguments.GaussianRightHalfPlaneArgumentLocalBound

/-!
# Uniform angle variation under a certified native displacement

The literal chart choices carry the direct, reciprocal, and boundary
comparisons to the unsigned argument. Conjugation is an isometry.
Opposite signs place both arguments near the positive real axis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentContinuity

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRightHalfPlaneArgument (nameF data source unsignedF unsignedData smallF smallData largeF largeData
  wide wide_zero wide_one)
open GaussianRightHalfPlaneArgumentChartContinuity (small_distance large_distance mixed_distance)
open GaussianRightHalfPlaneArgumentIncrementGeometry (step coordinates opposite_height small_ratio large_ratio mixed_ratios)
open LeanProofs.IPRA.Probability.Variance (ad)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open RationalArithmetic (select_zero select_one)
open RationalCubeMidpoint (fraction)
open RationalValueBounds (radius_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem unsigned_small_at (p A B : PTm n) (h : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    ap2 unsignedF p (unsignedData A B) ≐ ap2 smallF p (smallData A B) :=
  (GaussianNameBranch.sample_at smallF largeF p (wide A B) (smallData A B) (largeData A B)).eqTrans
    (select_zero _ _ _ (wide_zero A B h))

private theorem unsigned_large_at (p A B : PTm n) (h : Γ ⊢[PRAAx] lt A B) : Γ ⊢[PRAAx]
    ap2 unsignedF p (unsignedData A B) ≐ ap2 largeF p (largeData A B) :=
  (GaussianNameBranch.sample_at smallF largeF p (wide A B) (smallData A B) (largeData A B)).eqTrans
    (select_one _ _ _ (wide_one A B h))

theorem unsigned_distance (p A B a b H M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hMA : Γ ⊢[PRAAx] le M A) (hMa : Γ ⊢[PRAAx] le M a)
    (hr : Γ ⊢[PRAAx] le (ad a A) H) (hi : Γ ⊢[PRAAx] le (ad b B) H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 unsignedF p (unsignedData A B)) (ap2 unsignedF p (unsignedData a b))
      (num 8*H*unit p+num 18*M) (M*unit p) := by
  let U := unit p
  let D := M*U
  have hu := unit_positive (Γ := Γ) p
  have hd := positive_product M U hM hu
  have hA := le_trans hM hMA
  have ha := le_trans hM hMa
  have step₁ : Γ ⊢[PRAAx] le (num 4*H*U+two*M) (num 8*H*U+num 18*M) := by
    ipra_le 4*𝔞(H)*𝔞(U)+16*𝔞(M)
  have step₂ : Γ ⊢[PRAAx] le (num 4*H*U+num 14*M) (num 8*H*U+num 18*M) := by
    ipra_le 4*𝔞(H)*𝔞(U)+4*𝔞(M)
  refine .orE (lt_or_le A B) ?_ ?_
  · refine .orE (lt_or_le a b) ?_ ?_
    · have hB : (lt a b :: lt A B :: Γ) ⊢[PRAAx] le A B := le_of_lt Prf.hyp1
      have hb : (lt a b :: lt A B :: Γ) ⊢[PRAAx] le a b := le_of_lt Prf.hyp0
      have rat := large_ratio A B a b H M hM.wk.wk hMA.wk.wk hMa.wk.wk hB hb hr.wk.wk hi.wk.wk
      have old := large_distance p A B a b (two*H) M (le_trans hA.wk.wk hB) (le_trans ha.wk.wk hb) hB hb hM.wk.wk rat
      have moved : (lt a b :: lt A B :: Γ) ⊢[PRAAx] distanceBounded
        (ap2 unsignedF p (unsignedData A B)) (ap2 unsignedF p (unsignedData a b)) (num 4*H*U+num 14*M) D :=
        distance_congr (unsigned_large_at p A B Prf.hyp1).eqSymm
        (unsigned_large_at p a b Prf.hyp0).eqSymm (by ipra_ring) (.eqRefl D) old
      exact distance_radius_mono_same hd.wk.wk step₂.wk.wk moved
    · have hB : (le b a :: lt A B :: Γ) ⊢[PRAAx] le A B := le_of_lt Prf.hyp1
      have hb : (le b a :: lt A B :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
      have r' : (le b a :: lt A B :: Γ) ⊢[PRAAx] le (ad A a) H := le_congr (add_comm _ _) (.eqRefl H) hr.wk.wk
      have i' : (le b a :: lt A B :: Γ) ⊢[PRAAx] le (ad B b) H := le_congr (add_comm _ _) (.eqRefl H) hi.wk.wk
      have rat := mixed_ratios a b A B H M hM.wk.wk hMa.wk.wk hMA.wk.wk hb hB r' i'
      have old := mixed_distance p a b A B (two*H) M ha.wk.wk (le_trans hA.wk.wk hB) hb hB hM.wk.wk
        rat.andE₁ (radius_symmetric _ _ _ _ rat.andE₂)
      exact distance_congr (unsigned_large_at p A B Prf.hyp1).eqSymm
        (unsigned_small_at p a b hb).eqSymm (by ipra_ring) (.eqRefl D)
        (distance_symmetric _ _ _ _ hd.wk.wk old)
  · refine .orE (lt_or_le a b) ?_ ?_
    · have hB : (lt a b :: le B A :: Γ) ⊢[PRAAx] le B A := Prf.hyp1
      have hb : (lt a b :: le B A :: Γ) ⊢[PRAAx] le a b := le_of_lt Prf.hyp0
      have rat := mixed_ratios A B a b H M hM.wk.wk hMA.wk.wk hMa.wk.wk hB hb hr.wk.wk hi.wk.wk
      have old := mixed_distance p A B a b (two*H) M hA.wk.wk (le_trans ha.wk.wk hb) hB hb hM.wk.wk
        rat.andE₁ (radius_symmetric _ _ _ _ rat.andE₂)
      exact distance_congr (unsigned_small_at p A B hB).eqSymm
        (unsigned_large_at p a b Prf.hyp0).eqSymm (by ipra_ring) (.eqRefl D) old
    · have hB : (le b a :: le B A :: Γ) ⊢[PRAAx] le B A := Prf.hyp1
      have hb : (le b a :: le B A :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
      have rat := small_ratio A B a b H M hM.wk.wk hMA.wk.wk hMa.wk.wk hB hr.wk.wk hi.wk.wk
      have old := small_distance p A B a b (two*H) M hA.wk.wk ha.wk.wk hB hb hM.wk.wk rat
      have moved : (le b a :: le B A :: Γ) ⊢[PRAAx] distanceBounded
        (ap2 unsignedF p (unsignedData A B)) (ap2 unsignedF p (unsignedData a b)) (num 4*H*U+two*M) D :=
        distance_congr (unsigned_small_at p A B hB).eqSymm
        (unsigned_small_at p a b hb).eqSymm (by ipra_ring) (.eqRefl D) old
      exact distance_radius_mono_same hd.wk.wk step₁.wk.wk moved

private theorem positive_at (p A B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B neg) ≐ ap2 unsignedF p (unsignedData A B) :=
  (GaussianNameBranch.sample_at unsignedF (GaussianNameConjugation.nameF unsignedF) p neg
    (unsignedData A B) (unsignedData A B)).eqTrans (select_zero _ _ _ h)

private theorem negative_at (p A B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ one) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B neg) ≐ GaussianRationalConjugation.point (ap2 unsignedF p (unsignedData A B)) :=
  ((GaussianNameBranch.sample_at unsignedF (GaussianNameConjugation.nameF unsignedF) p neg
    (unsignedData A B) (unsignedData A B)).eqTrans (select_one _ _ _ h)).eqTrans
      (GaussianNameConjugation.sample_at unsignedF p (unsignedData A B))

private theorem across_axis (p A B neg a b sign H M : PTm n)
    (h : Γ ⊢[PRAAx] source A neg) (g : Γ ⊢[PRAAx] source a sign)
    (hM : Γ ⊢[PRAAx] le one M) (hMA : Γ ⊢[PRAAx] le M A) (hMa : Γ ⊢[PRAAx] le M a)
    (hSmall : Γ ⊢[PRAAx] le H M) (hB : Γ ⊢[PRAAx] le (B+b) H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B neg)) (ap2 nameF p (data a b sign))
      (num 8*H*unit p+num 18*M) (M*unit p) := by
  let x := ap2 nameF p (data A B neg)
  let y := ap2 nameF p (data a b sign)
  let U := unit p
  have left := le_trans (le_add_right B b) hB
  have right := le_trans (le_add_left b B) hB
  have oldX := GaussianRightHalfPlaneArgumentLocalBound.sample_bound p A B neg h.andE₁
    (le_trans left (le_trans hSmall hMA)) h.andE₂
  have oldY := GaussianRightHalfPlaneArgumentLocalBound.sample_bound p a b sign g.andE₁
    (le_trans right (le_trans hSmall hMa)) g.andE₂
  have bx := bounded_radius_mono x B A B M h.andE₁ hM (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl B) hMA) oldX
  have by' := bounded_radius_mono y b a b M g.andE₁ hM (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl b) hMa) oldY
  have joined := distance_triangle_same x qzero y B b M hM
    ((GaussianReconstructionRoots.distance_zero_iff x B M hM).iffMpr bx)
    (distance_symmetric _ _ _ _ hM ((GaussianReconstructionRoots.distance_zero_iff y b M hM).iffMpr by'))
  exact distance_radius_mono x y (B+b) M (num 8*H*U+num 18*M) (M*U) hM
    (positive_product _ _ hM (unit_positive p))
    (by ipra_le (𝔞(M)*𝔞(U))*sl hB+7*𝔞(H)*𝔞(U)*𝔞(M)+18*𝔞(M)^2) joined

theorem distance_at (p A B neg a b sign H M : PTm n)
    (h : Γ ⊢[PRAAx] source A neg) (g : Γ ⊢[PRAAx] source a sign)
    (hM : Γ ⊢[PRAAx] le one M) (hMA : Γ ⊢[PRAAx] le M A) (hMa : Γ ⊢[PRAAx] le M a)
    (hSmall : Γ ⊢[PRAAx] le H M)
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (step A B neg a b sign) H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B neg)) (ap2 nameF p (data a b sign))
      (num 8*H*unit p+num 18*M) (M*unit p) := by
  let x := ap2 unsignedF p (unsignedData A B)
  let y := ap2 unsignedF p (unsignedData a b)
  have c := coordinates A B neg a b sign H h.andE₂ g.andE₂ hw
  have ud := unsigned_distance p A B a b H M hM hMA hMa c.andE₁ c.andE₂
  have nd := GaussianRationalConjugation.point_distance x y _ _ (positive_product _ _ hM (unit_positive p)) ud
  refine .orE h.andE₂ ?_ ?_
  · refine .orE g.andE₂.wk ?_ ?_
    · exact distance_congr (positive_at p A B neg Prf.hyp1).eqSymm (positive_at p a b sign Prf.hyp0).eqSymm
        (.eqRefl _) (.eqRefl _) ud.wk.wk
    · exact across_axis p A B neg a b sign H M h.wk.wk g.wk.wk hM.wk.wk hMA.wk.wk hMa.wk.wk hSmall.wk.wk
        (opposite_height A B neg a b sign H (.orI₁ (.andI Prf.hyp1 Prf.hyp0)) hw.wk.wk)
  · refine .orE g.andE₂.wk ?_ ?_
    · exact across_axis p A B neg a b sign H M h.wk.wk g.wk.wk hM.wk.wk hMA.wk.wk hMa.wk.wk hSmall.wk.wk
        (opposite_height A B neg a b sign H (.orI₂ (.andI Prf.hyp1 Prf.hyp0)) hw.wk.wk)
    · exact distance_congr (negative_at p A B neg Prf.hyp1).eqSymm (negative_at p a b sign Prf.hyp0).eqSymm
        (.eqRefl _) (.eqRefl _) nd.wk.wk

theorem actual_right_half_plane_argument_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 2) ⟶ source (var 3) (var 5) ⟶
      (le one (var 7) ⋏ (le (var 7) (var 0) ⋏ (le (var 7) (var 3) ⋏ le (var 6) (var 7)))) ⟶
      ComplexLogarithmRemainder.bounded (step (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6) ⟶
      distanceBounded (ap2 nameF (var 8) (data (var 0) (var 1) (var 2)))
        (ap2 nameF (var 8) (data (var 3) (var 4) (var 5)))
        (num 8*var 6*unit (var 8)+num 18*var 7) (var 7*unit (var 8))) := by
  refine closeUniv 9 (.impI (.impI (.impI (.impI ?_))))
  exact distance_at _ _ _ _ _ _ _ _ _ (Prf.hyp0.wk.wk.wk) (Prf.hyp0.wk.wk)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentContinuity
