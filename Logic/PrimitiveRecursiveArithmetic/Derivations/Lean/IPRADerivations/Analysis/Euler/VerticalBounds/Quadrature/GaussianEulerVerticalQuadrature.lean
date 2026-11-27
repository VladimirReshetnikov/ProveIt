import IPRADerivations.Analysis.Euler.VerticalBounds.Integrands.GaussianEulerVerticalPointwise
import IPRADerivations.Analysis.Integration.Quadrature.GaussianPositiveRadiusQuadrature
import IPRADerivations.Analysis.Euler.CompactExhaustion.Names.GaussianEulerImproperName

/-!
# Vertical domination of the original Euler quadrature observations

The complex argument and its native real projection use the same original
grid, including the cutoff and compact integration clocks. Pointwise
Euclidean domination sums with exactly the interval width times the row
allowance. Both readbacks use the unchanged literal programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalQuadrature

open_ipra
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerIntegrandName (evaluatorF fixedData sample)
open GaussianCompactRiemannName (quadrature precision sampleBody sampleData sample_body_at)
open GaussianPositiveRadiusFiniteSum (boundBy bound_congr rowBounds)
open GaussianPositiveRadiusQuadrature (correctedBody corrected_row)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowData (p N a C E z B : PTm n) : PTm n := sampleData p N a C E (fixedData z B)

ipra_subst rowData

theorem row_readback (i p N a C E z B : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i (rowData p N a C E z B) ≐ sample p z B (a*N+C*i) (E*N) :=
  sample_body_at _ _ _ _ _ _ _ _

theorem original_grid_rows (p N a C E z R B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rowBounds (sampleBody evaluatorF) (correctedBody (sampleBody evaluatorF)) N (rowData p N a C E z B)
      (pairT (rowData p N a C E (argument z) B) (radiusPoint (num 4) (unit p))) := by
  let sh := fun q : PTm n => Syn.shift q
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hh : Δ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source (sh z) (sh R) (sh B) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source (sh z) (sh R) (sh B) := by
      simpa [Fm.shift,Syn.shift,sh] using h.shift
    exact e.wk
  have aa : Δ ⊢[PRAAx] le one (sh a) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh a) := by simpa [Fm.shift,Syn.shift,sh,one] using ha.shift
    exact e.wk
  have ee : Δ ⊢[PRAAx] le one (sh E) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,sh,one] using hE.shift
    exact e.wk
  have nn : Δ ⊢[PRAAx] le one (sh N) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
    exact e.wk
  let c := sh a*sh N+sh C*var 0
  let d := sh E*sh N
  let r := radiusPoint (num 4) (unit (sh p))
  have hc : Δ ⊢[PRAAx] le one c := le_trans (positive_product _ _ aa nn) (le_add_right _ _)
  have hd : Δ ⊢[PRAAx] le one d := positive_product _ _ ee nn
  have pointwise := GaussianEulerVerticalPointwise.original_row_bound (sh p) (sh z) (sh R) (sh B) c d (.andI hh (.andI hc hd))
  have actual := row_readback (Γ := Δ) (var 0) (sh p) (sh N) (sh a) (sh C) (sh E) (sh z) (sh B)
  have real := row_readback (Γ := Δ) (var 0) (sh p) (sh N) (sh a) (sh C) (sh E) (argument (sh z)) (sh B)
  have correction := corrected_row (Γ := Δ) (sampleBody evaluatorF) (var 0)
    (rowData (sh p) (sh N) (sh a) (sh C) (sh E) (argument (sh z)) (sh B)) r
  refine .allI (.impI ?_)
  simpa [rowBounds,Syn.shift,sh,Δ,r] using
    bound_congr actual.eqSymm (correction.eqTrans (qadd_congr real (.eqRefl r))).eqSymm pointwise

theorem original_grid_bound (p N a C E z R B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    boundBy (quadrature evaluatorF p N a C E (fixedData z B))
      (qadd (quadrature evaluatorF p N a C E (fixedData (argument z) B)) (radiusPoint (C*num 4) (E*unit p))) :=
  GaussianPositiveRadiusQuadrature.weighted_bound _ _ N _ _ C E (num 4) (unit p) hN hE (unit_positive p)
    (original_grid_rows p N a C E z R B h ha hE hN)

def cutoffRadius (t k A R : PTm n) : PTm n :=
  radiusPoint (width k A R*num 4) (etaDen k A R*unit (precision t (top k A R)))

theorem cutoff_radius_budget (t k A R : PTm n) : Γ ⊢[PRAAx]
    le (width k A R*num 4*unit t) (etaDen k A R*unit (precision t (top k A R))) := by
  let E := etaDen k A R
  let T := top k A R
  let C := width k A R
  have four : Γ ⊢[PRAAx] le (num 4) (unit (num 6)) :=
    le_trans (le_of_eq_add (d := num 3) (by ipra_ring)) (RationalClosure.succ_le_two_pow (num 6))
  have allowance : Γ ⊢[PRAAx] le (num 4*unit t) (unit (t+num 6)) :=
    le_congr (.eqRefl _) ((pw_add two t (num 6)).eqTrans (LeanProofs.IPRA.mul_comm _ _)).eqSymm
      (LeanProofs.IPRA.mul_le_mul_right (unit t) four)
  have timeAllowance : Γ ⊢[PRAAx] le (T*(num 4*unit t)) (unit (precision t T)) :=
    le_trans (le_congr (LeanProofs.IPRA.mul_comm _ _) (.eqRefl _) (LeanProofs.IPRA.mul_le_mul_right T allowance))
      (GaussianCompactRiemannName.precision_lower t T)
  exact le_trans (le_congr (by ipra_ring : Γ ⊢[PRAAx] C*(num 4*unit t) ≐ C*num 4*unit t)
      (by ipra_ring : Γ ⊢[PRAAx] E*T*(num 4*unit t) ≐ (T*(num 4*unit t))*E)
      (LeanProofs.IPRA.mul_le_mul_right (num 4*unit t) (GaussianGammaCompactQuadratureBoundary.width_bound k A R)))
    (le_congr (.eqRefl _) (LeanProofs.IPRA.mul_comm _ _) (LeanProofs.IPRA.mul_le_mul_right E timeAllowance))

theorem original_compact_bound (t k z R B A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) : Γ ⊢[PRAAx]
    boundBy (ap2 GaussianGammaEulerCompactQuadrature.nameF t (GaussianGammaEulerCompactQuadrature.data z R B k A))
      (qadd (ap2 GaussianGammaEulerCompactQuadrature.nameF t (GaussianGammaEulerCompactQuadrature.data (argument z) R B k A))
        (cutoffRadius t k A R)) := by
  let E := etaDen k A R
  let T := top k A R
  let C := width k A R
  let M := GaussianGammaEulerCompactQuadrature.conservativeCells t k A R
  have grid := original_grid_bound (precision t T) M one C E z R B h (le_refl one)
    (GaussianGammaIntegralCutoffs.eta_den_positive k A R) (GaussianCompactRiemannName.mesh_positive _ _ _)
  exact bound_congr (GaussianGammaEulerCompactQuadrature.original_sample t z R B k A).eqSymm
    (qadd_congr (GaussianGammaEulerCompactQuadrature.original_sample t (argument z) R B k A).eqSymm (.eqRefl _)) grid

theorem original_improper_bound (p z R B A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) : Γ ⊢[PRAAx]
    boundBy (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
      (qadd (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data (argument z) R B A))
        (cutoffRadius (p+num 4) p A R)) :=
  bound_congr (GaussianEulerImproperName.original_observation p z R B A).eqSymm
    (qadd_congr (GaussianEulerImproperName.original_observation p (argument z) R B A).eqSymm (.eqRefl _))
    (original_compact_bound (p+num 4) p z R B A h)

theorem original_improper_Euler_vertical_same_query_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianEulerUpperPowerCoefficients.source (var 1) (var 2) (var 3) ⟶
      boundBy (ap2 GaussianEulerImproperName.nameF (var 0) (GaussianEulerImproperName.data (var 1) (var 2) (var 3) (var 4)))
        (qadd (ap2 GaussianEulerImproperName.nameF (var 0)
          (GaussianEulerImproperName.data (argument (var 1)) (var 2) (var 3) (var 4)))
          (cutoffRadius (var 0+num 4) (var 0) (var 4) (var 2)))) :=
  closeUniv 5 (.impI (original_improper_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalQuadrature
