import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareMappedInterval
import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareJacobianCompactName
import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareCorrectedComparison
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# Compact Euler change of variables for the quadratic map

The two original compact samplers are compared on a common refinement.
The target refinement is the square map's exact polynomial block grid.
The left-endpoint Jacobian error uses a uniform bound on the actual
mapped Euler samples. The final names retain both requested precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareCompactComparison

open_ipra
open GaussianRationalQuadratureSquarePartition (lowerNumerator widthNumerator intervalDenominator fineCount cellCap)
open GaussianEulerSquareTimeGeometry (upperEndpoint majorant)
open GaussianCompactRiemannName (mesh precision quadrature grid quadrature_index_congr)
open GaussianEulerSquareJacobianRate (query)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T c d : PTm n) : Fm PTm n :=
  GaussianEulerSquareMappedInterval.source z R B a C E T c d ⋏ le one C
def imageData (z R B a C E T c d : PTm n) : PTm n :=
  GaussianEulerCompactAdditivity.data z R B (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) (upperEndpoint c T)
def envelope (R a C E T c d : PTm n) : PTm n :=
  num 3+cellCap c a C*(GaussianEulerCompactModulus.lipschitz R (intervalDenominator d E) (upperEndpoint c T)*cellCap c a C+two)+
    (c*C*C*majorant R E T c d)+num 3

ipra_subst source
ipra_subst imageData
ipra_subst envelope

private theorem row_bounds (p N z R B a C E T c d : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerSquareMappedInterval.source z R B a C E T c d) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianRationalQuadratureSquareJacobian.rowBounds evaluatorF p N c d a C E (fixedData z B) (majorant R E T c d) := by
  let sh (u : PTm n) := Syn.shift u
  have H : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerSquareMappedInterval.source (sh z) (sh R) (sh B) (sh a) (sh C)
      (sh E) (sh T) (sh c) (sh d) := by simpa only [Fm.shift,Syn.shift,sh,GaussianEulerSquareMappedInterval.subst_source] using hs.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hN.shift
  refine .allI (.impI ?_)
  let u : PTm (n+1) := grid (var 0) (sh N) (sh a) (sh C) (sh E)
  have ht := GaussianCompactRiemannName.grid_inside (var 0) (sh N) (sh a) (sh C) (sh E)
    H.andE₁.andE₂.andE₁.wk H.andE₁.andE₁.andE₂.andE₁.wk hn.wk (le_of_lt Prf.hyp0)
  have hu := GaussianEulerCompactAdditivity.domain_of_inside u (sh a) (sh C) (sh E) (sh T)
    H.andE₁.andE₂.andE₁.wk H.andE₁.andE₁.andE₂.andE₁.wk H.andE₁.andE₂.andE₂.wk ht
  have point := GaussianEulerSquareTimeGeometry.original_mapped_observation_bound (sh p) (sh z) (sh R) (sh B)
    (sh E) (sh T) (sh c) (sh d) (fstT u) (sndT u) (.andI H.andE₁.andE₁.wk H.andE₂.wk) hu
  have readback := GaussianRationalQuadratureSquareJacobian.actual_mapped_row
    (Γ := lt (var 0) (sh N) :: Γ.map Fm.shift) evaluatorF (var 0) (sh p)
    (sh N) (sh c) (sh d) (sh a) (sh C) (sh E) (fixedData (sh z) (sh B))
  simpa only [GaussianRationalQuadratureSquareJacobian.rowBounds,GaussianUniformFiniteSumBound.summandsBounded,
    GaussianCompactRiemannName.subst_sampleData,GaussianRationalQuadratureDilation.subst_pullData,
    GaussianEulerIntegrandName.subst_fixedData,GaussianEulerSquareTimeGeometry.subst_majorant,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh] using
    (GaussianRationalReciprocal.bound_congr readback.eqSymm (.eqRefl _) (.eqRefl _) point)

theorem original_diagonal (t z R B a C E T c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T c d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianEulerCompactAdditivity.nameF t (imageData z R B a C E T c d))
      (ap2 GaussianEulerSquareJacobianCompactName.nameF t (GaussianEulerSquareJacobianCompactName.data z R B c d a C E T))
      (envelope R a C E T c d) (unit t) := by
  let A := lowerNumerator c a
  let W := widthNumerator c a C
  let F := intervalDenominator d E
  let S := upperEndpoint c T
  let L := GaussianEulerCompactModulus.lipschitz R F S
  let J := GaussianEulerSquareJacobianRate.lipschitz R E T c d
  let O := mesh t L S
  let K := mesh t J T
  let N := O*K
  let M := GaussianEulerSquareTimeGeometry.majorant R E T c d
  let s := precision t S+precision t T
  let q := query s T c
  let U := unit t
  let x := fixedData z B
  let y := GaussianEulerSquareJacobianCompactName.fixedData z B c d T
  have hc := hs.andE₁.andE₂.andE₁
  have hd := hs.andE₁.andE₂.andE₂
  have ha := hs.andE₁.andE₁.andE₂.andE₁
  have hE := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  have hO : Γ ⊢[PRAAx] le one O := GaussianCompactRiemannName.mesh_positive _ _ _
  have hK : Γ ⊢[PRAAx] le one K := GaussianCompactRiemannName.mesh_positive _ _ _
  have hN := positive_product _ _ hO hK
  have hF : Γ ⊢[PRAAx] le one F := positive_product _ _ (positive_product _ _ hd hE) hE
  have hStrict : Γ ⊢[PRAAx] GaussianRationalQuadratureSquarePartition.source c d a C E N :=
    .andI hc (.andI ha (.andI hs.andE₂ (.andI hd (.andI hE hN))))
  have hW : Γ ⊢[PRAAx] le one W := GaussianRationalQuadratureSquarePartition.width_positive c d a C E N hStrict
  have hR : Γ ⊢[PRAAx] le one (W*O*K*K) := positive_product _ _ (positive_product _ _ (positive_product _ _ hW hO) hK) hK
  have hp := unit_positive (Γ := Γ) t
  have hShift := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) t (t+num 6) (le_add_right _ _)
  have meshLower : Γ ⊢[PRAAx] le (unit (t+num 6)) O := le_of_eq_add (d := unit (t+num 6)*L*S*S) (by unfold O mesh; ipra_ring)
  have hUN : Γ ⊢[PRAAx] le U N := le_trans (le_trans hShift meshLower)
    (le_congr (by ipra_ring) (by unfold N; ipra_ring) (mul_le_mul_right O hK))
  have hsq : Γ ⊢[PRAAx] le s q := le_add_right _ _
  have leftLate : Γ ⊢[PRAAx] le (precision t S) q := le_trans (le_add_right _ _) hsq
  have rightLate : Γ ⊢[PRAAx] le (precision t T) s := le_add_left _ _
  have hUq := GaussianCompactRiemannName.dyadic_monotone t q
    (le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) leftLate)
  have image := GaussianEulerSquareMappedInterval.original_interval z R B a C E T c d hs.andE₁
  have old := GaussianEulerCompactAdditivity.compact_input z R B A W F S image
  have retimed := GaussianEulerSquareJacobianCompactName.compact_input z R B c d a C E T hs.andE₁
  have first := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF t q (W*O*K*K) A W F L S x old hR leftLate
  have last := GaussianCompactMeshIndependence.arbitrary_refinement GaussianEulerSquareJacobianCompactName.evaluatorF
    t s O a C E J T y retimed hO rightLate
  have imageFine := quadrature_index_congr (Γ := Γ) evaluatorF q ((W*O*K*K)*O) (fineCount N c a C) A W F x
    (by unfold fineCount N W; ipra_ring)
  have oldAt : Γ ⊢[PRAAx] ap2 GaussianEulerCompactAdditivity.nameF t (imageData z R B a C E T c d) ≐
      GaussianCompactRiemannName.sample evaluatorF t A W F L S x := GaussianCompactRiemannName.name_at _ _ _ _ _ _ _ _
  have newAt := GaussianEulerSquareJacobianCompactName.name_at (Γ := Γ) t z R B c d a C E T
  have rightFine := GaussianEulerSquareJacobianCompactName.quadrature_at (Γ := Γ) s N z B c d a C E T
  have commonPos := unit_positive (Γ := Γ) (t+num 6)
  have move := mul_le_mul_right (num 3) hShift
  have left := distance_symmetric _ _ _ _ hp (distance_radius_mono _ _ _ _ _ _ commonPos hp
    (le_congr (mul_comm _ _) (mul_comm _ _) move) (distance_congr imageFine oldAt.eqSymm (.eqRefl _) (.eqRefl _) first))
  have right := distance_radius_mono _ _ _ _ _ _ commonPos hp (le_congr (mul_comm _ _) (mul_comm _ _) move)
    (distance_congr rightFine newAt.eqSymm (.eqRefl _) (.eqRefl _) last)
  have raw := GaussianRationalQuadratureSquareCorrectedComparison.original_Euler_finite_comparison q z R B N c d a C E S (.andI hStrict image)
  have rawDen := positive_product _ _ hF (positive_product _ _ (positive_product _ _ hF hN) (unit_positive q))
  have middle := distance_radius_mono _ _ _ _ _ _ rawDen hp
    (GaussianEulerSquareMappedInterval.partition_budget (cellCap c a C) L F N U (unit q) hF hUN hUq) raw
  have jac := GaussianRationalQuadratureSquareJacobian.original_finite_jacobian_bound evaluatorF q N c d a C E x M
    (.andI hd (.andI hE hN)) (row_bounds q N z R B a C E T c d hs.andE₁ hN)
  have jacDen := positive_product _ _ hF hN
  have corrected := distance_radius_mono _ _ _ _ _ _ jacDen hp
    (GaussianEulerSquareMappedInterval.jacobian_budget c C M d E N U hd hE hUN) jac
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold envelope; dsimp only [L,F,S,M]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp left (distance_triangle_same _ _ _ _ _ _ hp middle
      (distance_triangle_same _ _ _ _ _ _ hp corrected right)))

theorem original_compact_cross (z R B a C E T c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T c d) :
    Γ ⊢[PRAAx] crossEquivalent GaussianEulerCompactAdditivity.nameF GaussianEulerSquareJacobianCompactName.nameF
      (imageData z R B a C E T c d) (GaussianEulerSquareJacobianCompactName.data z R B c d a C E T) := by
  refine GaussianNameRingLaws.equivalent_of_envelope GaussianEulerCompactAdditivity.nameF GaussianEulerSquareJacobianCompactName.nameF
    (imageData z R B a C E T c d) (GaussianEulerSquareJacobianCompactName.data z R B c d a C E T) (envelope R a C E T c d)
    (GaussianEulerCompactAdditivity.name_regular z R B _ _ _ _
      (GaussianEulerSquareMappedInterval.original_interval z R B a C E T c d hs.andE₁))
    (GaussianEulerSquareJacobianCompactName.name_regular z R B c d a C E T hs.andE₁) ?_
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have h : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) (sh c) (sh d) :=
    by simpa only [Fm.shift,subst_source,Syn.shift,sh] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_imageData,subst_envelope,
    GaussianEulerSquareJacobianCompactName.subst_data,Syn.shift,sh] using
    original_diagonal (var 0) (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) (sh c) (sh d) h

theorem actual_Euler_compact_quadratic_substitution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      crossEquivalent GaussianEulerCompactAdditivity.nameF GaussianEulerSquareJacobianCompactName.nameF
        (imageData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (GaussianEulerSquareJacobianCompactName.data (var 0) (var 1) (var 2) (var 7) (var 8) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 9 (.impI (original_compact_cross _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareCompactComparison
