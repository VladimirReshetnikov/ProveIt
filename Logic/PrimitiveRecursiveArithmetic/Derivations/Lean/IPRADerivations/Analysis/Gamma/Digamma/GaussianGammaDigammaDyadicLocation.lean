import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaDyadicEndpoints
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaSlopeLowerRational
import IPRADerivations.Analysis.Stirling.GaussianGammaHalfWallisRate
import IPRADerivations.Analysis.RationalArithmetic.RationalUpperRepresentation

/-!
# A primitive recursive location of the positive digamma zero

The left endpoint of the selected cell is the location observation.
Adjacent digamma samples have opposite signs, and their separation
gives the residual bound. For the location comparison, if the left
endpoint at one clock exceeds the right endpoint at the other clock,
the lower digamma slope bounds that excess using the two sample errors.
The two directed comparisons give a regular location name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicLocation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaDigammaDyadicCrossing (sample leftIndex adjacent_samples)
open GaussianGammaDigammaDyadicMesh (clock grid grid_positive grid_scale adjacent_upper)
open GaussianGammaDigammaDyadicEndpoints (endpoint_signs)
open GaussianGammaDigammaGridSign (zero_le_of_sign le_zero_of_negative near_zero_left)
open GaussianGammaDigammaSlopeLowerRational (domain quarterGap lower_slope_rational_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalHorner (qadd qzero positive_product ofGaussian_canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qzero_add)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalGaussianRealPart (real_add real_zero)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_order_left upper_order_right radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def index (p : PTm n) : PTm n := leftIndex (clock p) (grid p)
def lower (p : PTm n) : PTm n := grid p+index p
def higher (p : PTm n) : PTm n := grid p+succ (index p)
def location (p : PTm n) : PTm n := fraction (lower p) (grid p)
def locationF : PR 2 := PTm.toPR (location (var 0))

@[simp] theorem subst_index {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) :
    Syn.subst σ (index p) = index (Syn.subst σ p) := by simp [index]
@[simp] theorem subst_lower {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) :
    Syn.subst σ (lower p) = lower (Syn.subst σ p) := by simp [lower]
@[simp] theorem subst_location {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) :
    Syn.subst σ (location p) = location (Syn.subst σ p) := by simp [location]

theorem location_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 locationF p x ≐ location p := by
  simpa [locationF, ap2] using toPR_eq (Γ := Γ) (location (var 0) : PTm 2) ![p,x]

theorem selected_cell (p : PTm n) : Γ ⊢[PRAAx] lt (index p) (grid p) ⋏
    (neg (sign (sample (clock p) (grid p) (index p))) ⋏
      sign (sample (clock p) (grid p) (succ (index p)))) := by
  have h := endpoint_signs (Γ := Γ) p
  exact adjacent_samples _ _ h.andE₁ h.andE₂

theorem residual_at (p : PTm n) : Γ ⊢[PRAAx]
    radius (sample (clock p) (grid p) (index p)) scalarZero (num 4) (grid p) := by
  have signs := (selected_cell (Γ := Γ) p).andE₂
  exact near_zero_left _ _ _ _ signs.andE₁ signs.andE₂ (adjacent_upper _ _)

private theorem higher_eq (p : PTm n) : Γ ⊢[PRAAx] higher p ≐ lower p+one := by
  unfold higher lower
  ipra_ring

private theorem lower_ceiling (p : PTm n) : Γ ⊢[PRAAx] le (lower p) (two*grid p) := by
  have h := le_of_lt (selected_cell (Γ := Γ) p).andE₁
  unfold lower
  ipra_le sl h

private theorem quarter_upper (p q : PTm n)
    (h : Γ ⊢[PRAAx] le (grid q*higher p) (grid p*lower q)) : Γ ⊢[PRAAx]
    upper (fstT (quarterGap (higher p) (grid p) (lower q) (grid q))) scalarZero
      (num 4*(grid p+grid q)) (grid p*grid q) := by
  let a := higher p
  let b := grid p
  let c := lower q
  let d := grid q
  let m := quarterGap a b c d
  let x := ap2 DF (clock p) (dd a b)
  let y := ap2 DF (clock q) (dd c d)
  have dom : Γ ⊢[PRAAx] domain a b c d :=
    .andI (grid_positive p) (.andI (le_add_right _ _) (.andI (grid_positive q)
      (.andI (le_add_right _ _) (.andI h (lower_ceiling q)))))
  have source := lower_slope_rational_at a b c d (clock p) (clock q) dom
  have hx : Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT x) :=
    rationalLE_congr real_zero.eqSymm (.eqRefl _)
      (zero_le_of_sign _ (selected_cell (Γ := Γ) p).andE₂.andE₂)
  have hy : Γ ⊢[PRAAx] rationalLE (fstT y) scalarZero :=
    le_zero_of_negative _ (selected_cell (Γ := Γ) q).andE₂.andE₁
  have hd : Γ ⊢[PRAAx] le one (num 4*b*d) :=
    positive_product _ _ (positive_product _ _ (by ipra_le 3) (grid_positive p)) (grid_positive q)
  have hm : Γ ⊢[PRAAx] GaussianRationalHorner.canonical m := ofGaussian_canonical _ _ hd
  have added := GaussianStirlingTailComparison.point_add_order qzero x m m hx (RationalArgmin.reflexive _)
  have moved := rationalLE_congr (congrFst (qzero_add m hm)) (real_add x m) added
  exact upper_order_right _ _ _ _ _ (upper_order_left _ _ _ _ _ moved source) hy

private theorem excess (p q : PTm n)
    (h : Γ ⊢[PRAAx] le (grid q*higher p) (grid p*lower q)) : Γ ⊢[PRAAx]
    le (monus (lower q*grid p) (higher p*grid q)) (num 16*(grid p+grid q)) := by
  let B := grid p
  let D := grid q
  let W := monus (lower q*B) (higher p*D)
  let T := num 4*B*D
  let A := num 4*(B+D)
  let M := B*D
  let point := fstT (quarterGap (higher p) B (lower q) D)
  have hT : Γ ⊢[PRAAx] le one T :=
    positive_product _ _ (positive_product _ _ (by ipra_le 3) (grid_positive p)) (grid_positive q)
  have repr : Γ ⊢[PRAAx] RationalArithmetic.represents point (ZT.ofNat W) T :=
    GaussianGammaDigammaHarmonicCells.point_fraction_represents W T hT
  let u := ZT.ofNat (M*one)*ZT.ofNat W
  let v := ZT.ofNat (M*T)*ZT.ofNat ConciseIPRA.PTm.zero+ZT.ofNat (A*T*one)
  have signed : Γ ⊢[PRAAx] zle u v :=
    RationalUpperRepresentation.upper_from_representations point scalarZero T one A M
      (ZT.ofNat W) (ZT.ofNat ConciseIPRA.PTm.zero) repr (scalar_zero_represents one) (quarter_upper p q h)
  apply RationalValueBounds.positive_cancel (positive_product _ _ (grid_positive p) (grid_positive q))
  refine le_of_eq_add (d := monus (v.pos+u.neg) (u.pos+v.neg)) ?_
  have e := zle_toZ signed
  apply deriveNat
  change ZT.toZ Γ (ZT.ofNat (M*one)*ZT.ofNat W)+𝔞(monus (v.pos+u.neg) (u.pos+v.neg)) =
    ZT.toZ Γ (ZT.ofNat (M*T)*ZT.ofNat ConciseIPRA.PTm.zero+ZT.ofNat (A*T*one)) at e
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_ofNat] at e
  dsimp only [A,M,T] at e ⊢
  ipra_simps
  linear_combination -e

theorem directed_location_gap (p q : PTm n) : Γ ⊢[PRAAx]
    le (lower q*grid p) (lower p*grid q+num 17*(grid p+grid q)) := by
  let u := lower q*grid p
  let v := higher p*grid q
  let w := lower p*grid q
  let s := grid p+grid q
  have e := natEq (higher_eq (Γ := Γ) p)
  have cap : Γ ⊢[PRAAx] le (v+num 16*s) (w+num 17*s) := by
    ipra_le 𝔞(grid p) using
      dsimp only [v,w,s]
      ipra_simps
      linear_combination -𝔞(grid q)*e
  refine .orE (le_total u v) ?_ ?_
  · exact le_trans Prf.hyp0 (le_trans (le_add_right _ _) cap.wk)
  · have h : le v u :: Γ ⊢[PRAAx] le (grid q*higher p) (grid p*lower q) :=
      le_congr (mul_comm _ _) (mul_comm _ _) Prf.hyp0
    have sum : le v u :: Γ ⊢[PRAAx] le (v+monus u v) (v+num 16*s) :=
      le_congr (add_comm _ _) (add_comm _ _) (add_le_add_right v (excess p q h))
    exact le_trans (le_congr (eq_add_of_le Prf.hyp0).eqSymm (.eqRefl _) sum) cap.wk

private theorem observation_bound (p q : PTm n) : Γ ⊢[PRAAx]
    le ((unit p*unit q)*(lower p*grid q))
      ((unit p*unit q)*(lower q*grid p)+(unit p+unit q)*grid p*grid q) := by
  have h := directed_location_gap (Γ := Γ) q p
  have ep := natEq (grid_scale (Γ := Γ) p)
  have eq := natEq (grid_scale (Γ := Γ) q)
  ipra_le 𝔞(unit p)*𝔞(unit q)*sl h+3008*𝔞(unit p)*𝔞(unit q)*(𝔞(unit p)+𝔞(unit q)) using
    rw [ep,eq]
    ring

theorem location_cauchy_at (p q : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (location p) (location q) (unit p+unit q) (unit p*unit q) := by
  have h := observation_bound (Γ := Γ) q p
  exact GaussianGammaHalfWallisRate.fraction_distance _ _ _ _ _ _
    (grid_positive p) (grid_positive q)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (observation_bound p q)
    (le_congr (by ipra_ring) (by ipra_ring) h)

theorem location_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN locationF x := by
  refine .allI (.allI ?_)
  exact GaussianRationalDistanceOrder.distance_congr (location_at _ _).eqSymm (location_at _ _).eqSymm
    (.eqRefl _) (.eqRefl _) (location_cauchy_at (var 1) (var 0))

theorem actual_original_digamma_dyadic_location_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] pointCN locationF ConciseIPRA.PTm.zero :=
  location_regular _

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicLocation
