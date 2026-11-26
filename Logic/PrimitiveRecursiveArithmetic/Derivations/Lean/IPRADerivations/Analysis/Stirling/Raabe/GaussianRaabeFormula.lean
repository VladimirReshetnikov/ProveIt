import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabePositiveComparison
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# Raabe's formula at every positive rational input

Each observation reads the original real log-Gamma quadrature on the
unit interval. A four-bit padding makes its cofinal error compatible
with the standard independent-precision name equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 860000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeFormula

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans point_at)
open GaussianPositiveRationalLogarithm (source)
open GaussianRaabeCofinalSchedule (clock clock_later)
open GaussianRaabePositiveComparison (value)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => GaussianRaabeRightSide.nameF
local notation "fd" => GaussianRaabeRightSide.data

def data (A D : PTm n) : PTm n := pairT A D
def nameF : PR 2 := PTm.toPR (value (var 0+num 4) (fstT (var 1)) (sndT (var 1)) : PTm 2)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A D : PTm n) :
    Syn.subst σ (data A D) = data (Syn.subst σ A) (Syn.subst σ D) := by simp [data]

theorem sample_at (p A D : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data A D) ≐ value (p+num 4) A D := by
  let h := p+num 4
  let x := data A D
  have raw : Γ ⊢[PRAAx] ap2 nameF p x ≐ value h (fstT x) (sndT x) := by
    let body : PTm 2 := value (var 0+num 4) (fstT (var 1)) (sndT (var 1))
    have body_eq : Syn.subst ![p,x] body = value h (fstT x) (sndT x) := by
      dsimp only [body]
      rw [GaussianRaabePositiveComparison.subst_value, PTm.subst_add, PTm.subst_num,
        subst_fstT, subst_sndT]
      rfl
    change Γ ⊢[PRAAx] ap2 (PTm.toPR body) p x ≐ value h (fstT x) (sndT x)
    rw [← body_eq]
    exact toPR_eq (Γ := Γ) body ![p,x]
  let body : PTm 3 := value (var 0) (var 1) (var 2)
  let u : Fin 3 → PTm n := ![h,fstT x,sndT x]
  let v : Fin 3 → PTm n := ![h,A,D]
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) body (σ := u) (σ' := v) (fun i => by
    fin_cases i
    · exact .eqRefl h
    · exact fst_pair A D
    · exact snd_pair A D)
  have left : Syn.subst u body = value h (fstT x) (sndT x) := by
    dsimp only [body]
    rw [GaussianRaabePositiveComparison.subst_value]
    rfl
  have right : Syn.subst v body = value h A D := by
    dsimp only [body]
    rw [GaussianRaabePositiveComparison.subst_value]
    rfl
  rw [left,right] at eq
  exact raw.eqTrans eq

theorem independent_observations (p s A D w : PTm n) (hs : Γ ⊢[PRAAx] source A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A D)) (ap2 F s (fd A D w))
      (unit p+unit s) (unit p*unit s) := by
  let h := p+num 4
  let k := clock h A D
  let U := unit p
  let V := unit s
  let W := unit h
  let K := unit k
  let r := value h A D
  let f := ap2 F k (fd A D w)
  let g := ap2 F s (fd A D w)
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) s
  have hw := unit_positive (Γ := Γ) h
  have hk := unit_positive (Γ := Γ) k
  have hwv := positive_product _ _ hw hv
  have later : Γ ⊢[PRAAx] le W K := GaussianExponentialReference.unit_monotone (clock_later h A D)
  have left : Γ ⊢[PRAAx] distanceBounded r f (num 14*V) (W*V) :=
    distance_radius_mono _ _ _ _ _ _ hw hwv (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
      (GaussianRaabePositiveComparison.observation_error h A D w hs)
  have right : Γ ⊢[PRAAx] distanceBounded f g (W+V) (W*V) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hk hv) hwv
      (by change Γ ⊢[PRAAx] le ((K+V)*(W*V)) ((W+V)*(K*V)); ipra_le 𝔞(V*V)*sl later)
      (point_at F (fd A D w) k s (GaussianRaabeRightSide.regular A D w hs))
  have padding : Γ ⊢[PRAAx] W ≐ num 16*U := by
    have pad : Γ ⊢[PRAAx] unit (num 4) ≐ num 16 :=
      LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 4
    exact ((pw_add two p (num 4)).eqTrans (congrMul (.eqRefl U) pad)).eqTrans (mul_comm _ _)
  have room : Γ ⊢[PRAAx] le (num 15*U) W :=
    le_congr (.eqRefl _) padding.eqSymm (by ipra_le 𝔞(U))
  have out : Γ ⊢[PRAAx] distanceBounded r g (U+V) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ hwv (positive_product _ _ hu hv)
      (by change Γ ⊢[PRAAx] le ((num 14*V+(W+V))*(U*V)) ((U+V)*(W*V)); ipra_le 𝔞(V*V)*sl room)
      (distance_triangle_same r f g _ _ _ hwv left right)
  exact distance_congr (sample_at p A D).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) out

theorem equivalent (A D w : PTm n) (hs : Γ ⊢[PRAAx] source A D) :
    Γ ⊢[PRAAx] crossEquivalent nameF F (data A D) (fd A D w) := by
  refine .allI (.allI ?_)
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have head : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh A) (sh D) :=
    by simpa only [sh,Fm.shift,Syn.shift,GaussianPositiveRationalLogarithm.subst_source] using hs.shift.shift
  simpa only [crossEquivalent,Syn.shift,sh,subst_data,GaussianRaabeRightSide.subst_data] using
    independent_observations (var 1) (var 0) (sh A) (sh D) (sh w) head

theorem regular (A D : PTm n) (hs : Γ ⊢[PRAAx] source A D) :
    Γ ⊢[PRAAx] pointCN nameF (data A D) := by
  let w : PTm n := ConciseIPRA.PTm.zero
  have e := equivalent A D w hs
  exact cross_trans nameF F nameF (data A D) (fd A D w) (data A D) e
    (cross_symm nameF F (data A D) (fd A D w) e)

theorem actual_Raabe_positive_rational_formula_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶
      crossEquivalent nameF F (data (var 0) (var 1)) (fd (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (equivalent _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRaabeFormula
