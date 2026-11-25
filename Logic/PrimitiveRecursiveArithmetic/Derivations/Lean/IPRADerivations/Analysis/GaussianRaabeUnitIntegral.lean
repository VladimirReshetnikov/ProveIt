import IPRADerivations.Analysis.GaussianRaabeOriginComparison
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# The improper log-Gamma integral on the unit interval

The name observes the original truncated log-Gamma quadratures on
[2⁻ʰ, 1]. Padding their precision makes the finite Raabe error
compatible with independent observations of ½ log(2π).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeUnitIntegral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans point_at)
open GaussianRaabeOriginComparison (value)
open GaussianRaabeOriginSchedule (clock)
open GaussianRaabeStirlingRemainder (constantSample)
open GaussianRaabeUnitStripBound (cost)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianStirlingConstant.nameF
local notation "fd" => GaussianStirlingConstant.nameData

def nameF : PR 2 := PTm.toPR (value (var 0+num 6) (var 1) : PTm 2)

theorem sample_at (p w : PTm n) : Γ ⊢[PRAAx] ap2 nameF p w ≐ value (p+num 6) w := by
  let body : PTm 2 := value (var 0+num 6) (var 1)
  have body_eq : Syn.subst ![p,w] body = value (p+num 6) w := by
    dsimp only [body]
    rw [GaussianRaabeOriginComparison.subst_value, PTm.subst_add, PTm.subst_num]
    rfl
  change Γ ⊢[PRAAx] ap2 (PTm.toPR body) p w ≐ value (p+num 6) w
  rw [← body_eq]
  exact toPR_eq (Γ := Γ) body ![p,w]

theorem independent_observations (p s w : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p w) (ap2 F s (fd w))
      (unit p+unit s) (unit p*unit s) := by
  let h := p+num 6
  let C := cost w
  let E := unit (GaussianRaabeOriginSchedule.cutoff h C)
  let N := GaussianRaabeOriginSchedule.fullMesh h C
  let k := clock h C
  let U := unit p
  let V := unit s
  let W := unit h
  let K := unit k
  let r := value h w
  let f := constantSample k w
  let g := constantSample s w
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) s
  have hw := unit_positive (Γ := Γ) h
  have hk := unit_positive (Γ := Γ) k
  have hwv := positive_product _ _ hw hv
  have later : Γ ⊢[PRAAx] le W K :=
    GaussianExponentialReference.unit_monotone (GaussianRaabeCofinalSchedule.clockFor_later h N E E)
  have left : Γ ⊢[PRAAx] distanceBounded r f (num 39*V) (W*V) :=
    distance_radius_mono _ _ _ _ _ _ hw hwv (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianRaabeOriginComparison.observation_error h w)
  have right : Γ ⊢[PRAAx] distanceBounded f g (W+V) (W*V) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hk hv) hwv
      (by
        change Γ ⊢[PRAAx] le ((K+V)*(W*V)) ((W+V)*(K*V))
        ipra_le 𝔞(V*V)*sl later)
      (point_at F (fd w) k s (GaussianStirlingConstant.name_regular w))
  have padding : Γ ⊢[PRAAx] W ≐ num 64*U := by
    have pad : Γ ⊢[PRAAx] unit (num 6) ≐ num 64 :=
      LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 6
    exact ((pw_add two p (num 6)).eqTrans (congrMul (.eqRefl U) pad)).eqTrans (mul_comm _ _)
  have room : Γ ⊢[PRAAx] le (num 40*U) W :=
    le_congr (.eqRefl _) padding.eqSymm (by ipra_le 24*𝔞(U))
  have out : Γ ⊢[PRAAx] distanceBounded r g (U+V) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ hwv (positive_product _ _ hu hv)
      (by
        change Γ ⊢[PRAAx] le ((num 39*V+(W+V))*(U*V)) ((U+V)*(W*V))
        ipra_le 𝔞(V*V)*sl room)
      (distance_triangle_same r f g _ _ _ hwv left right)
  exact distance_congr (sample_at p w).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) out

theorem equivalent (w : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF F w (fd w) := by
  refine .allI (.allI ?_)
  simpa only [crossEquivalent, Syn.shift, GaussianStirlingConstant.subst_nameData] using
    (independent_observations (Γ := (Γ.map Fm.shift).map Fm.shift)
      (var 1) (var 0) (Syn.shift (Syn.shift w)))

theorem regular (w : PTm n) : Γ ⊢[PRAAx] pointCN nameF w :=
  cross_trans nameF F nameF w (fd w) w (equivalent w) (cross_symm nameF F w (fd w) (equivalent w))

theorem actual_unit_log_Gamma_integral_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN nameF (var 0) ⋏ crossEquivalent nameF F (var 0) (fd (var 0))) :=
  closeUniv 1 (.andI (regular _) (equivalent _))

end LeanProofs.IPRA.Analysis.GaussianRaabeUnitIntegral
