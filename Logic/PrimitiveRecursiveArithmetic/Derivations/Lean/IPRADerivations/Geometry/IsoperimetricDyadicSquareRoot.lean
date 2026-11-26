import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.RationalSquareRootBounds
import IPRADerivations.Core.OrderCertificates

/-!
# The dyadic square-root bracket used in polygonal isoperimetry

For the original nonnegative rational input (A/B), compute the numerator
of the lower endpoint by integer square root after division. The integer
certificate proves that the returned numerator is the greatest one admitted
by the source comparison, and that the next dyadic point is strictly above.
The denominator is exactly (2^t).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Geometry.IsoperimetricDyadicSquareRoot

open_ipra
open LeanProofs.IPRA.Analysis
open RationalArgmin (rationalLE rationalLE_congr)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalSquareRootBounds (square fraction_square)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scale (t : PTm n) : PTm n := pw two t
def scaled (A t : PTm n) : PTm n := A * (scale t * scale t)
def index (A B t : PTm n) : PTm n := isqrt (quo (scaled A t) B)
def sd (A B t : PTm n) : PTm n := fraction (index A B t) (scale t)
def upper (A B t : PTm n) : PTm n := fraction (succ (index A B t)) (scale t)

ipra_subst scale [two, one]
ipra_subst scaled
ipra_subst index
ipra_subst sd
ipra_subst upper

theorem scale_positive (t : PTm n) : Γ ⊢[PRAAx] le one (scale t) :=
  RationalNonnegativePowers.denominator_positive two t (by ipra_le 1)

theorem index_bracket (A B t : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le (B * (index A B t * index A B t)) (scaled A t) ⋏
      lt (scaled A t) (B * (succ (index A B t) * succ (index A B t))) := by
  let z := scaled A t
  let q := quo z B
  let r := rem z B
  let j := index A B t
  have hb := pos_of_eq_succ ((eq_add_of_le hB).eqTrans (by ipra_ring))
  have div : Γ ⊢[PRAAx] (z ≐ B*q+r) ⋏ lt r B := div_mod_at hb
  have lo : Γ ⊢[PRAAx] le (j*j) q := isqrt_le q
  have hi : Γ ⊢[PRAAx] lt q (succ j*succ j) :=
    lt_congr (.eqRefl _) (congrMul (succ_eq_add_one j) (succ_eq_add_one j)).eqSymm (lt_isqrt_succ_sq q)
  refine .andI ?_ ?_
  · have h := mul_le_mul_right B lo
    exact le_trans (le_congr (mul_comm _ _) (mul_comm _ _) h)
      (le_congr (.eqRefl _) (Prf.andE₁ div).eqSymm (le_add_right _ _))
  · have h1 : Γ ⊢[PRAAx] lt z (B * succ q) := by
      have h := Prf.andE₂ div
      have hi' : Γ ⊢[PRAAx] le (succ (B*q+r)) (B*succ q) := by ipra_le sl h
      exact lt_congr (Prf.andE₁ div).eqSymm (.eqRefl _) hi'
    exact lt_of_lt_of_le h1
      (mul_le_mul_left B hi)

theorem index_greatest (A B t k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le (B*(k*k)) (scaled A t)) : Γ ⊢[PRAAx] le k (index A B t) := by
  refine .orE (lt_or_le (index A B t) k) ?_ Prf.hyp0
  have h := sq_le_sq (Γ := lt (index A B t) k :: Γ) Prf.hyp0
  have h' := mul_le_mul_right B h
  exact le_lt_absurd _ (le_trans (le_congr (mul_comm _ _) (mul_comm _ _) h') hk.wk)
    (.andE₂ (index_bracket _ _ _ hB.wk))

theorem index_fits_bound (A B t M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] lt (scaled A t) (B*(M*M))) : Γ ⊢[PRAAx] le (index A B t) M := by
  refine .orE (lt_or_le M (index A B t)) ?_ Prf.hyp0
  have h := sq_le_sq (le_of_lt (Γ := lt M (index A B t) :: Γ) Prf.hyp0)
  have h' := mul_le_mul_right B h
  exact le_lt_absurd _ (le_trans (le_congr (mul_comm _ _) (mul_comm _ _) h')
    (.andE₁ (index_bracket _ _ _ hB.wk))) hM.wk

theorem rational_bracket (A B t : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    rationalLE (square (sd A B t)) (fraction A B) ⋏
      neg (rationalLE (square (upper A B t)) (fraction A B)) := by
  let H := scale t
  let j := index A B t
  have hH := scale_positive (Γ := Γ) t
  have hHH := positive_product H H hH hH
  have h := index_bracket A B t hB
  refine .andI ?_ (.impI ?_)
  · exact rationalLE_congr (fraction_square j H hH).eqSymm (.eqRefl _)
      (fraction_order _ _ _ _ hHH hB (.andE₁ h))
  · have cmp := rationalLE_congr (fraction_square (succ j) H hH).wk (.eqRefl (fraction A B)) Prf.hyp0
    have bad := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (fraction_represents (succ j*succ j) (H*H) hHH).wk (fraction_represents A B hB).wk cmp
    exact le_lt_absurd _ bad (Prf.andE₂ h).wk

def sourceBound (A t : PTm n) : PTm n := scale t * succ A

theorem source_bound_strict (A B t : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    lt (scaled A t) (B * (sourceBound A t * sourceBound A t)) := by
  let H := scale t
  have hH := scale_positive (Γ := Γ) t
  have hHH := positive_product H H hH hH
  have hStep : Γ ⊢[PRAAx] lt (A*(H*H)) (succ A*(H*H)) := by
    change Γ ⊢[PRAAx] le (succ (A*(H*H))) (succ A*(H*H))
    ipra_le sl hHH
  have hScale : Γ ⊢[PRAAx] le (succ A*(H*H)) ((H*succ A)*(H*succ A)) := by
    exact le_of_eq_add (d := A*succ A*H*H) (by ipra_ring)
  have hMul : Γ ⊢[PRAAx] le (sourceBound A t * sourceBound A t) (B * (sourceBound A t * sourceBound A t)) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ hB)
  exact lt_of_lt_of_le hStep (le_trans hScale hMul)

theorem unit_interval_bound (A B t : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx] le (index A B t) (scale t) := by
  let j := index A B t
  let H := scale t
  have mulBound : Γ ⊢[PRAAx] le (B*(j*j)) (B*(H*H)) :=
    le_trans (.andE₁ (index_bracket _ _ _ hB)) (mul_le_mul_right _ h)
  have sqBound := RationalValueBounds.positive_cancel hB mulBound
  refine .orE (lt_or_le H j) ?_ Prf.hyp0
  have more := sq_le_sq (Γ := lt H j :: Γ) Prf.hyp0
  have strict : (lt H j :: Γ) ⊢[PRAAx] lt (H*H) (succ H*succ H) := by
    change (lt H j :: Γ) ⊢[PRAAx] le (succ (H*H)) (succ H*succ H)
    exact le_of_eq_add (d := H+H) (by ipra_ring)
  exact le_lt_absurd _ sqBound.wk (lt_of_lt_of_le strict more)

theorem upper_is_next (A B t : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.add (sd A B t) (fraction one (scale t)) ≐ upper A B t := by
  let H := scale t
  let j := index A B t
  have hH := scale_positive (Γ := Γ) t
  have lhs := GaussianRationalHorner.scalar_add_same _ _ _ _ H hH
    (fraction_represents j H hH) (fraction_represents one H hH)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hH) lhs (fraction_represents (succ j) H hH) hH hH
  ipra_lc

def output (A B t : PTm n) : PTm n := pairT (index A B t) (pairT (sd A B t) (upper A B t))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (A B t : PTm n) : PTm n := ap3 outputF A B t

theorem program_at (A B t : PTm n) : Γ ⊢[PRAAx] run A B t ≐ output A B t := by
  simpa [run,outputF,output,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![A,B,t]

theorem actual_dyadic_square_root_bracket_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      rationalLE (square (sd (var 0) (var 1) (var 2))) (fraction (var 0) (var 1)) ⋏
      neg (rationalLE (square (upper (var 0) (var 1) (var 2))) (fraction (var 0) (var 1)))) :=
  closeUniv 3 (.impI (rational_bracket _ _ _ Prf.hyp0))

theorem actual_dyadic_square_root_source_maximum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le ((var 1) * (var 3 * var 3)) (scaled (var 0) (var 2)) ⟶
      le (var 3) (index (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (index_greatest _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_dyadic_square_root_source_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      le (index (var 0) (var 1) (var 2)) (sourceBound (var 0) (var 2))) :=
  closeUniv 3 (.impI (index_fits_bound _ _ _ _ Prf.hyp0 (source_bound_strict _ _ _ Prf.hyp0)))

theorem actual_dyadic_square_root_unit_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ le (index (var 0) (var 1) (var 2)) (scale (var 2))) :=
  closeUniv 3 (.impI (.impI (unit_interval_bound _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_dyadic_square_root_next_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArithmetic.add (sd (var 0) (var 1) (var 2)) (fraction one (scale (var 2))) ≐
      upper (var 0) (var 1) (var 2)) :=
  closeUniv 3 (upper_is_next _ _ _)

theorem actual_dyadic_square_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Geometry.IsoperimetricDyadicSquareRoot
