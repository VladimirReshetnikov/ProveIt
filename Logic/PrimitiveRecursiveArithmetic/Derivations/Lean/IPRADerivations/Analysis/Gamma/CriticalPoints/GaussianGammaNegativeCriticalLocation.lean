import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalLocationComparison
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalGrid

/-!
# The regular primitive recursive location in each negative interval

Compare the nonnegative right sample of one selected cell to the negative
left sample of another. The quarter slope bounds any excess of the second
left endpoint over the first right endpoint. This excess plus the width of
the first cell fits the ordinary two independent observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaDigammaDyadicMesh (clock grid_scale)
open GaussianGammaDigammaGridSign (zero_le_of_sign le_zero_of_negative)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData mesh mesh_minimum)
open GaussianGammaNegativeCriticalGrid (denominator numerator leftIndex grid_guard selected location locationF location_at)
open GaussianGammaNegativeCriticalLocationComparison (domain margin mixed_lower_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qzero ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianStirlingTailComparison (point_add_order)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalGaussianRealPart (real_zero real_add)
open RationalValueBounds (upper upper_order_left upper_order_right positive_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def lower (p N : PTm n) : PTm n := numerator p (leftIndex p N)
def higher (p N : PTm n) : PTm n := numerator p (succ (leftIndex p N))
def fractionLocation (p N : PTm n) : PTm n := fraction (lower p N) (denominator p N)
def fractionLocationF : PR 2 := PTm.toPR (fractionLocation (var 0) (var 1))

@[simp] theorem subst_lower {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (lower p N) = lower (Syn.subst σ p) (Syn.subst σ N) := by simp [lower]
@[simp] theorem subst_higher {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (higher p N) = higher (Syn.subst σ p) (Syn.subst σ N) := by simp [higher]
@[simp] theorem subst_fractionLocation {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (fractionLocation p N) = fractionLocation (Syn.subst σ p) (Syn.subst σ N) := by simp [fractionLocation]

theorem fraction_location_at (p N : PTm n) : Γ ⊢[PRAAx] ap2 fractionLocationF p N ≐ fractionLocation p N := by
  simpa only [fractionLocationF,ap2,subst_fractionLocation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (toPR_eq (Γ := Γ) (fractionLocation (var 0) (var 1) : PTm 2) ![p,N])

theorem denominator_positive (p N : PTm n) : Γ ⊢[PRAAx] le one (denominator p N) :=
  positive_product _ _ (unit_positive p) (le_trans (by ipra_le 7) (mesh_minimum N))

theorem lower_guard (p N : PTm n) : Γ ⊢[PRAAx] guard (lower p N) (denominator p N) :=
  grid_guard p N _ (le_of_lt (selected p N).andE₁)

theorem higher_guard (p N : PTm n) : Γ ⊢[PRAAx] guard (higher p N) (denominator p N) :=
  grid_guard p N _ (selected p N).andE₁

private theorem higher_eq (p N : PTm n) : Γ ⊢[PRAAx] higher p N ≐ lower p N+one := by
  unfold higher lower numerator
  ipra_ring

private theorem margin_upper (p q N : PTm n)
    (h : Γ ⊢[PRAAx] le (denominator q N*higher p N) (denominator p N*lower q N)) : Γ ⊢[PRAAx]
    upper (fstT (margin (higher p N) (denominator p N) (lower q N) (denominator q N))) scalarZero
      (num 4*unit (clock q)+unit (clock p)) (unit (clock p)*unit (clock q)) := by
  let a := higher p N
  let b := denominator p N
  let c := lower q N
  let d := denominator q N
  let m := margin a b c d
  let x := ap2 nameF (clock p) (nameData a b N)
  let y := ap2 nameF (clock q) (nameData c d N)
  have dom : Γ ⊢[PRAAx] domain a b c d := .andI (higher_guard p N) (.andI (lower_guard q N) h)
  have source := mixed_lower_at (clock p) (clock q) a b c d N dom
  have hx : Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT x) :=
    rationalLE_congr real_zero.eqSymm (.eqRefl _)
      (zero_le_of_sign _ (selected (Γ := Γ) p N).andE₂.andE₂)
  have hy : Γ ⊢[PRAAx] rationalLE (fstT y) scalarZero :=
    le_zero_of_negative _ (selected (Γ := Γ) q N).andE₂.andE₁
  have hd : Γ ⊢[PRAAx] le one (num 4*(d*b)) :=
    positive_product _ _ (by ipra_le 3) (positive_product _ _ (denominator_positive q N) (denominator_positive p N))
  have hm : Γ ⊢[PRAAx] GaussianRationalHorner.canonical m := ofGaussian_canonical _ _ hd
  have added := point_add_order qzero x m m hx (RationalArgmin.reflexive _)
  have moved := rationalLE_congr (congrFst (qzero_add m hm)) (real_add x m) added
  exact upper_order_right _ _ _ _ _ (upper_order_left _ _ _ _ _ moved source) hy

private theorem cross_excess (p q N : PTm n)
    (h : Γ ⊢[PRAAx] le (denominator q N*higher p N) (denominator p N*lower q N)) : Γ ⊢[PRAAx]
    le (num 16*(unit p*unit q)*monus (denominator p N*lower q N) (denominator q N*higher p N))
      ((num 4*unit q+unit p)*(denominator p N*denominator q N)) := by
  let B := denominator p N
  let D := denominator q N
  let W := monus (B*lower q N) (D*higher p N)
  let E := num 4*(D*B)
  let T := unit (clock p)*unit (clock q)
  let A := num 4*unit (clock q)+unit (clock p)
  let point := fstT (margin (higher p N) B (lower q N) D)
  have he : Γ ⊢[PRAAx] le one E :=
    positive_product _ _ (by ipra_le 3) (positive_product _ _ (denominator_positive q N) (denominator_positive p N))
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents point (ZT.ofNat W) E :=
    GaussianGammaDigammaHarmonicCells.point_fraction_represents W E he
  let l := ZT.ofNat (T*one)*ZT.ofNat W
  let r := ZT.ofNat (T*E)*ZT.ofNat zero+ZT.ofNat (A*E*one)
  have signed : Γ ⊢[PRAAx] zle l r :=
    RationalUpperRepresentation.upper_from_representations point scalarZero E one A T
      (ZT.ofNat W) (ZT.ofNat zero) rep (scalar_zero_represents one) (margin_upper p q N h)
  have cleared : Γ ⊢[PRAAx] le (T*W) (A*E) := by
    refine le_of_eq_add (d := PolynomialBisection.slack l r) ?_
    have e := zle_toZ signed
    apply deriveNat
    change ZT.toZ Γ (ZT.ofNat (T*one)*ZT.ofNat W)+𝔞(PolynomialBisection.slack l r) =
      ZT.toZ Γ (ZT.ofNat (T*E)*ZT.ofNat zero+ZT.ofNat (A*E*one)) at e
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
    ipra_simps
    linear_combination -e
  have eu := natEq (show Γ ⊢[PRAAx] unit (clock p) ≐ num 64*unit p from grid_scale p)
  have ev := natEq (show Γ ⊢[PRAAx] unit (clock q) ≐ num 64*unit q from grid_scale q)
  apply positive_cancel (c := num 256) (by ipra_le 255)
  change Γ ⊢[PRAAx] le (num 256*(num 16*(unit p*unit q)*W))
    (num 256*((num 4*unit q+unit p)*(B*D)))
  ipra_le sl cleared using
    dsimp only [T,A,E]
    ipra_simps
    rw [eu,ev]
    ring

theorem directed_gap (p q N : PTm n) : Γ ⊢[PRAAx]
    le ((unit p*unit q)*(lower q N*denominator p N))
      ((unit p*unit q)*(lower p N*denominator q N)+(unit p+unit q)*denominator p N*denominator q N) := by
  let S := unit p
  let T := unit q
  let B := denominator p N
  let D := denominator q N
  let u := lower q N*B
  let v := higher p N*D
  let w := lower p N*D
  have hm := mesh_minimum (Γ := Γ) N
  have e := natEq (higher_eq (Γ := Γ) p N)
  have cell : Γ ⊢[PRAAx] le (num 16*S*T*v) (num 16*S*T*w+two*T*B*D) := by
    ipra_le 2*𝔞(S)*𝔞(T)*𝔞(D)*sl hm using
      dsimp only [v,w,B,denominator,S]
      ipra_simps
      linear_combination -16*𝔞(unit p)*𝔞(T)*𝔞(D)*e
  apply positive_cancel (c := num 16) (by ipra_le 15)
  change Γ ⊢[PRAAx] le (num 16*(S*T*u)) (num 16*(S*T*w+(S+T)*B*D))
  refine .orE (le_total u v) ?_ ?_
  · have uv : le u v :: Γ ⊢[PRAAx] le u v := Prf.hyp0
    ipra_le 16*𝔞(S)*𝔞(T)*sl uv+sl cell.wk+(16*𝔞(S)+14*𝔞(T))*𝔞(B)*𝔞(D)
  · have vu : le v u :: Γ ⊢[PRAAx] le v u := Prf.hyp0
    have calcH := cross_excess p q N (le_congr (mul_comm _ _) (mul_comm _ _) vu)
    have excess : le v u :: Γ ⊢[PRAAx] le (num 16*S*T*monus u v) ((num 4*T+S)*(B*D)) :=
      le_congr (congrMul (by ipra_ring) (congrMonus (mul_comm _ _) (mul_comm _ _))) (.eqRefl _) calcH
    have eu := natEq (eq_add_of_le vu)
    ipra_le sl cell.wk+sl excess+(15*𝔞(S)+10*𝔞(T))*𝔞(B)*𝔞(D) with -16*𝔞(S)*𝔞(T)*eu

theorem fraction_location_cauchy_at (p q N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (fractionLocation p N) (fractionLocation q N) (unit p+unit q) (unit p*unit q) := by
  have hp := denominator_positive (Γ := Γ) p N
  have hq := denominator_positive (Γ := Γ) q N
  exact GaussianGammaHalfWallisRate.fraction_distance _ _ _ _ _ _ hp hq
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (le_congr (by ipra_ring) (by ipra_ring) (directed_gap q p N)) (le_congr (.eqRefl _) (by ipra_ring) (directed_gap p q N))

theorem location_cauchy_at (p q N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (location p N) (location q N) (unit p+unit q) (unit p*unit q) := by
  have h := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ h (fraction_location_cauchy_at p q N)
      (GaussianRationalPowerDifference.distance_refl_zero (fraction (succ N) one) _ h))

theorem fraction_location_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN fractionLocationF N := by
  refine .allI (.allI ?_)
  let w := Syn.shift (Syn.shift N)
  exact distance_congr (fraction_location_at (var 1) w).eqSymm (fraction_location_at (var 0) w).eqSymm
    (.eqRefl _) (.eqRefl _) (fraction_location_cauchy_at (var 1) (var 0) w)

theorem location_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN locationF N := by
  refine .allI (.allI ?_)
  let w := Syn.shift (Syn.shift N)
  exact distance_congr (location_at (var 1) w).eqSymm (location_at (var 0) w).eqSymm
    (.eqRefl _) (.eqRefl _) (location_cauchy_at (var 1) (var 0) w)

theorem original_shifted_negative_gamma_critical_location_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN locationF (var 0)) :=
  closeUniv 1 (location_regular _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocation
