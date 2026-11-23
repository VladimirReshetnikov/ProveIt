import IPRADerivations.Analysis.GaussianEulerUnitKernelVerticalPointwise
import IPRADerivations.Analysis.GaussianEulerUnitKernelCompactName
import IPRADerivations.Analysis.GaussianCompactPositiveRadiusObservations

/-!
# Source-only vertical domination of the actual compact unit kernel

Every original grid row is derived from the actual rational-time kernel
and its checked projected-real exponential comparison. The original
weighted finite sums and the actual original compact names retain both
requested queries. The real companion's lower envelope is derived, not
assumed. All interval sources permit zero width.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactDominance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelCompactName (source evaluatorF fixedData lipschitz nameF data)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianCompactRiemannName (sampleBody sampleData grid inside mesh precision)
open GaussianPositiveRadiusFiniteSum (boundBy bound_congr rowBounds)
open GaussianPositiveRadiusQuadrature (correctedBody)
open GaussianRationalHorner (qadd)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Projection preserves the same physical interval and numerical disk. -/
theorem projected_source (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    source (argument z) R B a C E G :=
  .andI (.andI h.andE₁.andE₁ (.andI h.andE₁.andE₂.andE₁
    (le_trans (GaussianEulerVerticalNativeProjection.norm_contraction z) h.andE₁.andE₂.andE₂))) h.andE₂

theorem evaluator_dominance (p t z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (ht : Γ ⊢[PRAAx] inside a C E t) : Γ ⊢[PRAAx]
    boundBy (ap3 evaluatorF p t (fixedData z B))
      (qadd (ap3 evaluatorF p t (fixedData (argument z) B)) (radiusPoint (num 4) (unit p))) := by
  have s := GaussianEulerUnitKernelCompactName.inside_source z R B a C E G t h ht
  have weak : Γ ⊢[PRAAx] GaussianEulerUnitKernelVerticalSquare.source z R B (fstT t) (sndT t) :=
    .andI (.andI s.andE₁.andE₁ s.andE₁.andE₂.andE₂) s.andE₂.andE₁
  exact bound_congr (GaussianEulerUnitKernelCompactName.evaluator_at p t z B).eqSymm
    (GaussianRationalSyntheticDivision.qadd_congr (GaussianEulerUnitKernelCompactName.evaluator_at p t (argument z) B).eqSymm (.eqRefl _))
    (GaussianEulerUnitKernelVerticalPointwise.original_named_bound p z R B (fstT t) (sndT t) weak)

theorem original_grid_rows (p N z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rowBounds (sampleBody evaluatorF) (correctedBody (sampleBody evaluatorF)) N
      (sampleData p N a C E (fixedData z B))
      (pairT (sampleData p N a C E (fixedData (argument z) B)) (radiusPoint (num 4) (unit p))) := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh G) := by
    have shifted : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh G) :=
      by simpa [Fm.shift,Syn.shift,sh] using h.shift
    exact shifted.wk
  have hn : Δ ⊢[PRAAx] le one (sh N) := by
    have shifted : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
    exact shifted.wk
  let t := grid (var 0) (sh N) (sh a) (sh C) (sh E)
  let r := radiusPoint (num 4) (unit (sh p))
  have time : Δ ⊢[PRAAx] inside (sh a) (sh C) (sh E) t := GaussianCompactRiemannName.grid_inside _ _ _ _ _
    (GaussianEulerUnitKernelCompactName.start_positive _ _ _ _ _ _ _ hs) hs.andE₂.andE₁ hn (le_of_lt Prf.hyp0)
  have bound := evaluator_dominance (sh p) t (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh G) hs time
  have left := GaussianCompactRiemannName.sample_body_at (Γ := Δ) evaluatorF (var 0) (sh p) (sh N) (sh a) (sh C) (sh E) (fixedData (sh z) (sh B))
  have right := GaussianCompactRiemannName.sample_body_at (Γ := Δ) evaluatorF (var 0) (sh p) (sh N) (sh a) (sh C) (sh E) (fixedData (argument (sh z)) (sh B))
  have corrected := GaussianPositiveRadiusQuadrature.corrected_row (Γ := Δ) (sampleBody evaluatorF) (var 0)
    (sampleData (sh p) (sh N) (sh a) (sh C) (sh E) (fixedData (argument (sh z)) (sh B))) r
  refine .allI (.impI ?_)
  simpa [rowBounds,Syn.shift,sh,Δ,r,t] using bound_congr left.eqSymm
    (corrected.eqTrans (GaussianRationalSyntheticDivision.qadd_congr right (.eqRefl r))).eqSymm bound

theorem original_grid_bound (p N z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    boundBy (GaussianCompactRiemannName.quadrature evaluatorF p N a C E (fixedData z B))
      (qadd (GaussianCompactRiemannName.quadrature evaluatorF p N a C E (fixedData (argument z) B))
        (radiusPoint (C*num 4) (E*unit p))) :=
  GaussianCompactPositiveRadiusDominance.original_finite_bound evaluatorF evaluatorF p N a C E _ _ hN h.andE₂.andE₁
    (original_grid_rows p N z R B a C E G h hN)

theorem compact_source (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    GaussianCompactPositiveRadiusDominance.source evaluatorF evaluatorF a C E (lipschitz R G) one
      (fixedData z B) (fixedData (argument z) B) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift G) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .andI (GaussianEulerUnitKernelCompactName.compact_input z R B a C E G h)
    (.andI (GaussianEulerUnitKernelCompactName.compact_input (argument z) R B a C E G (projected_source z R B a C E G h)) (.allI ?_))
  simpa only [GaussianCompactPositiveRadiusDominance.allRows,GaussianCompactPositiveRadiusDominance.rows,
    GaussianEulerUnitKernelCompactName.subst_fixedData,GaussianEulerUnitKernelCompactName.subst_lipschitz,
    GaussianEulerVerticalNativeProjection.subst_argument,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    original_grid_rows (precision (var 0) one) (mesh (var 0) (lipschitz (Syn.shift R) (Syn.shift G)) one)
      (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift G) hs
      (GaussianCompactRiemannName.mesh_positive (var 0) (lipschitz (Syn.shift R) (Syn.shift G)) one)

def radiusNumerator (p q z R B a C E G : PTm n) : PTm n :=
  GaussianCompactPositiveRadiusObservations.radiusNumerator evaluatorF p q a C E (lipschitz R G) one (fixedData (argument z) B)
def radiusDenominator (p q z R B a C E G : PTm n) : PTm n :=
  GaussianCompactPositiveRadiusObservations.radiusDenominator evaluatorF p q a C E (lipschitz R G) one (fixedData (argument z) B)
def realBound (p q z R B a C E G : PTm n) : PTm n :=
  GaussianCompactPositiveRadiusObservations.realBound evaluatorF p q a C E (lipschitz R G) one (fixedData (argument z) B)

theorem original_observations (p q z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data z R B a C E G)) (radiusNumerator p q z R B a C E G) (radiusDenominator p q z R B a C E G) :=
  GaussianCompactPositiveRadiusObservations.original_observations evaluatorF evaluatorF p q a C E (lipschitz R G) one _ _
    (compact_source z R B a C E G h)

theorem radius_value (p q z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (realBound p q z R B a C E G) (ZT.ofNat (radiusNumerator p q z R B a C E G))
      (radiusDenominator p q z R B a C E G) :=
  GaussianCompactPositiveRadiusObservations.radius_value evaluatorF evaluatorF p q a C E (lipschitz R G) one _ _
    (compact_source z R B a C E G h)

theorem original_companion_nonnegative (q z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    RationalValueBounds.upper RationalGaussianEmbedding.scalarZero (fstT (ap2 nameF q (data (argument z) R B a C E G))) one (unit q) :=
  GaussianCompactPositiveRadiusObservations.companion_lower evaluatorF evaluatorF q a C E (lipschitz R G) one _ _
    (compact_source z R B a C E G h)

theorem actual_original_compact_unit_kernel_vertical_dominance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) ⋏
      RationalArithmetic.represents (realBound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (ZT.ofNat (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (.andI (original_observations _ _ _ _ _ _ _ _ _ Prf.hyp0) (radius_value _ _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactDominance
