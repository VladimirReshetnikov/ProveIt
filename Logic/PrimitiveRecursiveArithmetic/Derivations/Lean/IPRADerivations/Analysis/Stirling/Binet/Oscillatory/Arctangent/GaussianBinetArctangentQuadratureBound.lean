import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentQuadrature
import IPRADerivations.Analysis.Inequalities.GaussianRationalFactorialEulerSums

/-!
# The exact arctangent quadrature majorant

Every original compact quadrature sample, at any encoded mesh, satisfies
`|∫₀ᵗ z/(z²+u²) du| ≤ t / Re(z)`. The pointwise bound is inherited
from the two resolvents and the finite sum uses the actual mesh weight.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentQuadratureBound

open_ipra
open GaussianBinetArctangentQuadrature (evaluatorF fixedData nameF data evaluator_at)
open GaussianCompactRiemannName (grid grid_inside sampleBody sampleData sample_body_at quadrature mesh mesh_positive precision)
open GaussianRationalRiemannRefinement (termsDistance constantBody sum_distance weight_bound)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem row_bound (p M X Y D sign A B i : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody evaluatorF) i (sampleData p M (B+zero) A B (fixedData X Y D sign)))
      (inst2 constantBody i qzero) D X := by
  let t := grid i M (B+zero) A B
  have inside := grid_inside i M (B+zero) A B (le_trans hB (le_add_right B zero)) hB hM (le_of_lt hi)
  have valueRead := (sample_body_at (Γ := Γ) evaluatorF i p M (B+zero) A B (fixedData X Y D sign)).eqTrans (evaluator_at p t X Y D sign)
  have row := GaussianBinetArctangentResolventRate.uniform_bound X Y D sign (GaussianBinetLaplaceStrip.tagNumerator t) (sndT t) hz inside.andE₂.andE₁
  rw [GaussianRationalRiemannRefinement.constant_entry]
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hz.andE₁.andE₁).iffMpr
    (bound_congr valueRead.eqSymm (.eqRefl _) (.eqRefl _) row)

theorem quadrature_bound (p M X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p M (B+zero) A B (fixedData X Y D sign)) (A*D) (B*X) := by
  let s (t : PTm n) := Syn.shift t
  have sz : Γ.map Fm.shift ⊢[PRAAx] source (s X) (s D) (s sign) := by
    simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift
  have sb : Γ.map Fm.shift ⊢[PRAAx] le one (s B) := by simpa [s,Fm.shift,Syn.shift] using hB.shift
  have sm : Γ.map Fm.shift ⊢[PRAAx] le one (s M) := by simpa [s,Fm.shift,Syn.shift] using hM.shift
  let x := sampleData p M (B+zero) A B (fixedData X Y D sign)
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody evaluatorF) constantBody M x qzero D X := by
    refine .allI (.impI ?_)
    simpa [s,x,Syn.shift] using row_bound (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B)
      (var 0) sz.wk sb.wk sm.wk Prf.hyp0
  have hX := hz.andE₁.andE₁
  have zeros : Γ ⊢[PRAAx] sum constantBody M qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero M).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value M)
  have norm : Γ ⊢[PRAAx] bounded (sum (sampleBody evaluatorF) M x) (M*D) X :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hX).iffMp
      (distance_congr (.eqRefl _) zeros (.eqRefl _) (.eqRefl _) (sum_distance _ _ _ _ _ _ _ hX rows))
  have hBM := positive_product _ _ hB hM
  have weighted := bounded_product _ _ _ _ _ _ hBM hX (weight_bound A B M hB hM) norm
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ (A*D) (B*X)
    (positive_product _ _ hBM hX) (positive_product _ _ hB hX)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) weighted

theorem name_bound (p X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data X Y D sign A B)) (A*D) (B*X) :=
  bound_congr (GaussianCompactRiemannName.name_at evaluatorF p (B+zero) A B (D*D) A (fixedData X Y D sign)).eqSymm
    (.eqRefl _) (.eqRefl _) (quadrature_bound (precision p A) (mesh p (D*D) A) X Y D sign A B hz hB (mesh_positive p (D*D) A))

theorem actual_Binet_arctangent_name_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 3) (var 4) ⋏ le one (var 6)) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) (var 5*var 3) (var 6*var 1)) :=
  closeUniv 7 (.impI (name_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentQuadratureBound
