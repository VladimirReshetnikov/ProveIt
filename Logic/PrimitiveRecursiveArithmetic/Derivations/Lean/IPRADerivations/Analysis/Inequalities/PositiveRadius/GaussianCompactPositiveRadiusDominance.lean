import IPRADerivations.Analysis.Integration.Quadrature.GaussianPositiveRadiusQuadrature
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveExponentialOrder

/-!
# Actual compact quadrature from positive real row majorants

The sole domination input concerns the original evaluated rows. Summing
and multiplying by the original positive weight retain the actual real
companion quadrature, with exactly four tolerances times interval width.
The same actual compact sampling mesh and query give a compact-name
statement. Zero width is allowed; no compact-output bound is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactPositiveRadiusDominance

open_ipra
open GaussianCompactRiemannName (quadrature sampleBody sampleData mesh precision input nameF data)
open GaussianPositiveRadiusFiniteSum (boundBy bound_congr rowBounds)
open GaussianPositiveRadiusQuadrature (correctedBody)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def correction (p C E T : PTm n) : PTm n := radiusPoint (C*num 4) (E*unit (precision p T))
def rows (F G : PR 3) (p a C E L T x y : PTm n) : Fm PTm n :=
  rowBounds (sampleBody F) (correctedBody (sampleBody G)) (mesh p L T)
    (sampleData (precision p T) (mesh p L T) a C E x)
    (pairT (sampleData (precision p T) (mesh p L T) a C E y) (radiusPoint (num 4) (unit (precision p T))))
def allRows (F G : PR 3) (a C E L T x y : PTm n) : Fm PTm n := .all
  (rows F G (var 0) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) (Syn.shift y))
def source (F G : PR 3) (a C E L T x y : PTm n) : Fm PTm n :=
  input F a C E L T x ⋏ (input G a C E L T y ⋏ allRows F G a C E L T x y)

ipra_subst correction
ipra_subst rows
ipra_subst allRows [Syn.subst_shift, Syn.shift_subst, Syn.up]
ipra_subst source

theorem original_finite_bound (F G : PR 3) (p N a C E x y : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] rowBounds (sampleBody F) (correctedBody (sampleBody G)) N
      (sampleData p N a C E x) (pairT (sampleData p N a C E y) (radiusPoint (num 4) (unit p)))) : Γ ⊢[PRAAx]
    boundBy (quadrature F p N a C E x)
      (qadd (quadrature G p N a C E y) (radiusPoint (C*num 4) (E*unit p))) :=
  GaussianPositiveRadiusQuadrature.weighted_bound (sampleBody F) (sampleBody G) N
    (sampleData p N a C E x) (sampleData p N a C E y) C E (num 4) (unit p) hN hE (unit_positive p) h

theorem rows_at (F G : PR 3) (p a C E L T x y : PTm n) (h : Γ ⊢[PRAAx] allRows F G a C E L T x y) :
    Γ ⊢[PRAAx] rows F G p a C E L T x y := by
  simpa [allRows] using h.allE p

theorem original_compact_bound (F G : PR 3) (p a C E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] source F G a C E L T x y) : Γ ⊢[PRAAx]
    boundBy (ap2 (nameF F) p (data a C E L T x))
      (qadd (ap2 (nameF G) p (data a C E L T y)) (correction p C E T)) :=
  bound_congr (GaussianCompactRiemannName.name_at F p a C E L T x).eqSymm
    (GaussianRationalSyntheticDivision.qadd_congr (GaussianCompactRiemannName.name_at G p a C E L T y).eqSymm (.eqRefl _))
    (original_finite_bound F G (precision p T) (mesh p L T) a C E x y
      (GaussianCompactRiemannName.mesh_positive p L T) h.andE₁.andE₂.andE₁
      (rows_at F G p a C E L T x y h.andE₂.andE₂))

theorem left_regular (F G : PR 3) (a C E L T x y : PTm n) (h : Γ ⊢[PRAAx] source F G a C E L T x y) :
    Γ ⊢[PRAAx] pointCN (nameF F) (data a C E L T x) :=
  GaussianCompactRiemannName.name_regular F a C E L T x h.andE₁

theorem right_regular (F G : PR 3) (a C E L T x y : PTm n) (h : Γ ⊢[PRAAx] source F G a C E L T x y) :
    Γ ⊢[PRAAx] pointCN (nameF G) (data a C E L T y) :=
  GaussianCompactRiemannName.name_regular G a C E L T y h.andE₂.andE₁

theorem correction_budget (p C E T : PTm n) (h : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    le (C*num 4*unit p) (E*unit (precision p T)) := by
  have four : Γ ⊢[PRAAx] le (num 4) (unit (num 6)) :=
    le_trans (le_of_eq_add (d := num 3) (by ipra_ring)) (RationalClosure.succ_le_two_pow (num 6))
  have allowance : Γ ⊢[PRAAx] le (num 4*unit p) (unit (p+num 6)) :=
    le_congr (.eqRefl _) ((pw_add two p (num 6)).eqTrans (LeanProofs.IPRA.mul_comm _ _)).eqSymm
      (LeanProofs.IPRA.mul_le_mul_right (unit p) four)
  have timeAllowance : Γ ⊢[PRAAx] le (T*(num 4*unit p)) (unit (precision p T)) :=
    le_trans (le_congr (LeanProofs.IPRA.mul_comm _ _) (.eqRefl _) (LeanProofs.IPRA.mul_le_mul_right T allowance))
      (GaussianCompactRiemannName.precision_lower p T)
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring) (LeanProofs.IPRA.mul_le_mul_right (num 4*unit p) h))
    (le_congr (.eqRefl _) (LeanProofs.IPRA.mul_comm _ _) (LeanProofs.IPRA.mul_le_mul_right E timeAllowance))

theorem correction_coordinate (p C E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (correction p C E T)) (fstT qzero) one (unit p) := by
  let D := E*unit (precision p T)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE (unit_positive _)
  have norm := bounded_radius_mono (correction p C E T) (C*num 4) D one (unit p) hD (unit_positive p)
    (le_congr (.eqRefl _) (by dsimp only [D]; ipra_ring) (correction_budget p C E T hC)) (radius_bounded _ _ hD)
  exact RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ (unit_positive p)
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive p)).iffMpr norm))

theorem actual_original_compact_row_domination_closed (F G : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      boundBy (ap2 (nameF F) (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (qadd (ap2 (nameF G) (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))
          (correction (var 0) (var 2) (var 3) (var 5)))) :=
  closeUniv 8 (.impI (original_compact_bound F G _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactPositiveRadiusDominance
