import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeFormula
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeNamedRightSide

/-!
# Raabe quadrature at the actual observations of a positive named input

Freeze the original input at a certified precision, decode its exact
rational base, and use the original log-Gamma quadrature on its unit
interval. The same observation compares to the named right side using
the quantitative frozen comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeNamedGrid

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedGammaPositiveLower (source)
open GaussianRaabeNamedRightSide (cost numerator denominator)
open GaussianRaabePositiveComparison (value)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem match_observations (x y z p s q K C : PTm n)
    (hK : Γ ⊢[PRAAx] le one K)
    (hclock : Γ ⊢[PRAAx] le (unit (p+num 4)) (unit q))
    (hbase : Γ ⊢[PRAAx] le (C*unit (p+num 4)) K)
    (grid : Γ ⊢[PRAAx] distanceBounded x y (num 14) (unit (p+num 4)))
    (rhs : Γ ⊢[PRAAx] distanceBounded z y (rateNumerator C K s q) (rateDenominator K s q)) :
    Γ ⊢[PRAAx] distanceBounded x z (unit p+unit s) (unit p*unit s) := by
  let h := p+num 4
  let U := unit p
  let V := unit s
  let Q := unit q
  let W := unit h
  have hw := unit_positive (Γ := Γ) h
  have hv := unit_positive (Γ := Γ) s
  have hu := unit_positive (Γ := Γ) p
  have hwv := positive_product _ _ hw hv
  have left : Γ ⊢[PRAAx] distanceBounded x y (num 14*V) (W*V) :=
    distance_radius_mono _ _ _ _ _ _ hw hwv (le_of_eq_add (d := zero) (by ipra_ring)) grid
  have rhden := denominator_positive K s q hK
  have right : Γ ⊢[PRAAx] distanceBounded y z (two*V+W) (W*V) :=
    distance_radius_mono _ _ _ _ _ _ rhden hwv
      (by
        change Γ ⊢[PRAAx] le ((C*V*Q+K*(V+Q))*(W*V)) ((two*V+W)*(K*V*Q))
        ipra_le 𝔞(V*V*Q)*sl hbase+𝔞(V*V*K)*sl hclock)
      (distance_symmetric _ _ _ _ rhden rhs)
  have padding : Γ ⊢[PRAAx] W ≐ num 16*U := by
    have pad : Γ ⊢[PRAAx] unit (num 4) ≐ num 16 :=
      LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 4
    exact ((pw_add two p (num 4)).eqTrans (congrMul (.eqRefl U) pad)).eqTrans (mul_comm _ _)
  have room : Γ ⊢[PRAAx] le (num 16*U) W :=
    le_congr (.eqRefl _) padding.eqSymm (le_refl _)
  have radius : Γ ⊢[PRAAx] le ((num 14*V+(two*V+W))*(U*V)) ((U+V)*(W*V)) := by
    ipra_le 𝔞(V*V)*sl room
  exact distance_radius_mono _ _ _ _ _ _ hwv (positive_product _ _ hu hv) radius
    (distance_triangle_same x y z _ _ _ hwv left right)


def data (x M : PTm n) : PTm n := pairT x M

ipra_subst data

def freezeClock (f : PR 2) (p x M : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (cost f x M) (p+num 4)

def gridValue (f : PR 2) (p x M : PTm n) : PTm n :=
  let k := freezeClock f p x M
  value (p+num 4) (numerator f k x M) (denominator f k x M)

ipra_subst gridValue [freezeClock]

def nameF (f : PR 2) : PR 2 :=
  PTm.toPR (gridValue f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

theorem base_at (f : PR 2) (p x M : PTm n) (hs : Γ ⊢[PRAAx] source f x M) :
    let k := freezeClock f p x M
    Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.fraction (numerator f k x M) (denominator f k x M) ≐
      ap2 f (k+GaussianNamedRightHalfPlane.threshold M) x :=
  GaussianRaabeNamedRightSide.fraction_at f (freezeClock f p x M) x M hs

theorem sample_at (f : PR 2) (p x M : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x M) ≐ gridValue f p x M := by
  let y := data x M
  let body : PTm 2 := gridValue f (var 0) (fstT (var 1)) (sndT (var 1))
  have read : Γ ⊢[PRAAx] ap2 (nameF f) p y ≐ gridValue f p (fstT y) (sndT y) := by
    have eq : Syn.subst ![p,y] body = gridValue f p (fstT y) (sndT y) := by
      dsimp only [body]
      rw [subst_gridValue, subst_fstT, subst_sndT]
      rfl
    change Γ ⊢[PRAAx] ap2 (PTm.toPR body) p y ≐ _
    rw [← eq]
    exact toPR_eq (Γ := Γ) body ![p,y]
  let term : PTm 3 := gridValue f (var 0) (var 1) (var 2)
  let a : Fin 3 → PTm n := ![p, fstT y, sndT y]
  let b : Fin 3 → PTm n := ![p, x, M]
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) term (σ := a) (σ' := b) (fun i => by
    fin_cases i
    · exact .eqRefl p
    · exact fst_pair x M
    · exact snd_pair x M)
  have left : Syn.subst a term = gridValue f p (fstT y) (sndT y) := by
    dsimp only [term]
    rw [subst_gridValue]
    rfl
  have right : Syn.subst b term = gridValue f p x M := by
    dsimp only [term]
    rw [subst_gridValue]
    rfl
  rw [left,right] at eq
  exact read.eqTrans eq

theorem frozen_grid_error (f : PR 2) (p s k x M w N : PTm n)
    (hs : Γ ⊢[PRAAx] source f x M) (hk : Γ ⊢[PRAAx] le (freezeClock f p x M) k)
    (mesh : Γ ⊢[PRAAx] le (GaussianRaabeCofinalSchedule.count (p+num 4)
      (numerator f k x M) (denominator f k x M)) N) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianRaabePositiveComparison.valueFor (p+num 4) N (numerator f k x M) (denominator f k x M))
      (ap2 (GaussianRaabeNamedRightSide.nameF f) s (GaussianRaabeNamedRightSide.data f x M w))
      (unit p+unit s) (unit p*unit s) := by
  let h := p+num 4
  let A := numerator f k x M
  let D := denominator f k x M
  let q := GaussianRaabeCofinalSchedule.clockFor h N A D
  let F := GaussianRaabeNamedRightSide.nameF f
  let X := GaussianRaabeNamedRightSide.data f x M w
  let G := GaussianRaabeRightSide.nameF
  let Y := GaussianRaabeRightSide.data A D w
  let C := cost f x M
  let r := GaussianRaabePositiveComparison.valueFor h N A D
  have guard : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D :=
    GaussianRaabeNamedRightSide.frozen_source f k x M hs
  have grid : Γ ⊢[PRAAx] distanceBounded r (ap2 G q Y) (num 14) (unit h) :=
    GaussianRaabePositiveComparison.observation_for h N A D w guard mesh
  have late : Γ ⊢[PRAAx] le (unit h) (unit q) :=
    GaussianExponentialReference.unit_monotone (GaussianRaabeCofinalSchedule.clockFor_later h N A D)
  have budget : Γ ⊢[PRAAx] le (C*unit h) (unit k) :=
    le_trans (GaussianFastValueCut.query_budget C h) (GaussianExponentialReference.unit_monotone hk)
  have rhs : Γ ⊢[PRAAx] distanceBounded (ap2 F s X) (ap2 G q Y)
      (rateNumerator C (unit k) s q) (rateDenominator (unit k) s q) :=
    rate_at F G X Y C (unit k) s q (GaussianRaabeNamedRightSide.frozen_rate f k x M w hs)
  exact match_observations r (ap2 G q Y) (ap2 F s X) p s q (unit k) C (unit_positive k) late budget grid rhs

theorem independent_observations (f : PR 2) (p s x M w : PTm n) (hs : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x M))
      (ap2 (GaussianRaabeNamedRightSide.nameF f) s (GaussianRaabeNamedRightSide.data f x M w))
      (unit p+unit s) (unit p*unit s) := by
  let k := freezeClock f p x M
  let N := GaussianRaabeCofinalSchedule.count (p+num 4) (numerator f k x M) (denominator f k x M)
  have estimate := frozen_grid_error f p s k x M w N hs (le_refl k) (le_refl N)
  exact distance_congr (sample_at f p x M).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) estimate

theorem equivalent (f : PR 2) (x M w : PTm n) (hs : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (GaussianRaabeNamedRightSide.nameF f)
      (data x M) (GaussianRaabeNamedRightSide.data f x M w) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have guard : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh M) := by
    simpa only [sh,Fm.shift,Syn.shift,GaussianNamedGammaPositiveLower.subst_source] using hs.shift.shift
  simpa only [crossEquivalent, Syn.shift, sh, subst_data, GaussianRaabeNamedRightSide.subst_data] using
    independent_observations f (var 1) (var 0) (sh x) (sh M) (sh w) guard

theorem regular (f : PR 2) (x M : PTm n) (hs : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x M) := by
  let G := GaussianRaabeNamedRightSide.nameF f
  let w : PTm n := zero
  let y := GaussianRaabeNamedRightSide.data f x M w
  have e := equivalent f x M w hs
  exact cross_trans (nameF f) G (nameF f) (data x M) y (data x M) e
    (cross_symm (nameF f) G (data x M) y e)

theorem actual_Raabe_named_frozen_grid_formula_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ crossEquivalent (nameF f) (GaussianRaabeNamedRightSide.nameF f)
        (data (var 0) (var 1)) (GaussianRaabeNamedRightSide.data f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (equivalent f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRaabeNamedGrid
