import IPRADerivations.Analysis.Gamma.Names.Symmetry.GaussianGammaRealValues
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlane
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder

/-!
# The actual positive real-part argument for vertical Euler comparisons

The existing real-axis projection program retains every original input
query. It preserves the positive real certificate and has canonical real
samples. Every projected observation stays inside the ORIGINAL input
disk U(f,x); no new projection radius is substituted for that disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalProjection

open_ipra
open GaussianGammaRealValues (projection axisF axis_sample_at axis_regular projection_distance)
open GaussianNamedRightHalfPlane (source certificate marginPoint)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (canonical qzero)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianExponentialSmallPerturbation (smallSamples)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem projected_coordinate (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 (axisF f) p x) ≐ RationalArithmetic.recode (fstT (ap2 f p x)) :=
  (axis_sample_at f p x).fstE

theorem coordinate_order (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 f p x)) (fstT (ap2 (axisF f) p x)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (projected_coordinate f p x).eqSymm
    (RationalArgmin.eq_le (RationalArithmetic.recode_equal _).eqSymm)

theorem projected_certificate (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] certificate f x A) : Γ ⊢[PRAAx]
    certificate (axisF f) x A := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] certificate f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  have old := real_order_at GaussianGammaCanonicalExponent.constantF f (marginPoint (Syn.shift (Syn.shift A)))
    (Syn.shift (Syn.shift x)) (var 1) (var 0) hs
  have order := coordinate_order (Γ := (Γ.map Fm.shift).map Fm.shift) f (var 0) (Syn.shift (Syn.shift x))
  have result := RationalValueBounds.upper_order_right
    (fstT (ap2 GaussianGammaCanonicalExponent.constantF (var 1) (marginPoint (Syn.shift (Syn.shift A)))))
    (fstT (ap2 f (var 0) (Syn.shift (Syn.shift x))))
    (fstT (ap2 (axisF f) (var 0) (Syn.shift (Syn.shift x)))) _ _ old order
  simpa only [certificate,realOrder,Syn.shift,GaussianNamedRightHalfPlane.subst_marginPoint] using result

theorem projected_source (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    source (axisF f) x A :=
  .andI (axis_regular f x h.andE₁) (.andI h.andE₂.andE₁ (projected_certificate f x A h.andE₂.andE₂))

theorem projected_real_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 (axisF f) p x) ⋏ RationalGaussianEmbedding.axis (ap2 (axisF f) p x) :=
  .andI (GaussianRationalHorner.canonical_congr (axis_sample_at f p x) (RationalGaussianEmbedding.embed_canonical _))
    (GaussianGammaRealValues.axis_sample_axis f p x)

theorem projected_real_samples (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] realSamples (axisF f) x := by
  refine .allI ?_
  simpa only [realSamples,Syn.shift] using projected_real_at f (var 0) (Syn.shift x)

theorem projection_zero : Γ ⊢[PRAAx] projection (qzero : PTm n) ≐ qzero :=
  (RationalGaussianRealPart.embed_congr RationalGaussianRealPart.real_zero).eqTrans RationalGaussianEmbedding.embed_zero

theorem projection_bound (q R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] bounded q R D) : Γ ⊢[PRAAx] bounded (projection q) R D :=
  (GaussianReconstructionRoots.distance_zero_iff (projection q) R D hD).iffMp
    (GaussianRationalDistanceOrder.distance_congr (.eqRefl (projection q)) (projection_zero (Γ := Γ)) (.eqRefl R) (.eqRefl D)
      (projection_distance q qzero R D hD ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr h)))

theorem original_disk_at (f : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    bounded (ap2 (axisF f) p x) (GaussianNameBounds.U f x) one :=
  GaussianRationalReciprocal.bound_congr (axis_sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _)
    (projection_bound _ _ _ (le_refl one) (GaussianNameBounds.sample_bound f x p h))

theorem original_disk (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    smallSamples (axisF f) x (GaussianNameBounds.U f x) one := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [smallSamples,GaussianNameBounds.subst_U,Syn.shift,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using original_disk_at f (var 0) (Syn.shift x) hs

theorem actual_vertical_positive_real_projection_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source f (var 0) (var 1) ⟶
      (source (axisF f) (var 0) (var 1) ⋏ (realSamples (axisF f) (var 0) ⋏
        smallSamples (axisF f) (var 0) (GaussianNameBounds.U f (var 0)) one))) :=
  closeUniv 2 (.impI (.andI (projected_source f _ _ Prf.hyp0)
    (.andI (projected_real_samples f _) (original_disk f _ Prf.hyp0.andE₁))))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalProjection
