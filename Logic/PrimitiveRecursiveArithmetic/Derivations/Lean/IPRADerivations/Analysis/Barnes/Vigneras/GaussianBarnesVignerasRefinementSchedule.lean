import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementChart

/-! Choose the fine grid only after fixing the analytic tolerance, far translation,
common disk, and supplied compact-strip modulus. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasRefinementChart (precision scheduled)
open GaussianBarnesVignerasRefinementJet (radius)
open GaussianBarnesVignerasRefinementWrap (observationClock translation)
open GaussianCoefficientNameBounds (unit)
open SignedDiscreteDerivativeOperators (width divisor)
open GaussianDiscreteDerivativeRounding (latticeScale)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "budget" => GaussianBarnesCanonicalPositiveLogarithmCalculus.budget
local notation "clock" => GaussianBarnesVignerasAdjacentObservation.clock
local notation "padding" => GaussianDiscretePeriodicDerivativeSchedule.padding

abbrev analytic (N p : PTm n) : PTm n := GaussianDiscretePeriodicDerivativeSchedule.clock N p

def farTranslation (N p : PTm n) : PTm n := GaussianBarnesVignerasCubicForce.translation (precision (analytic N p))

def widthFor (N p M : PTm n) : PTm n :=
  succ (budget (precision (analytic N p)) (farTranslation N p+num 6) one+M)

def divisorFor (N p M : PTm n) : PTm n := N*widthFor N p M

def config (N p M payload : PTm n) : PTm n :=
  let D := divisorFor N p M
  let q := analytic N p
  pairT (widthFor N p M) (pairT D (pairT (unit q*padding D)
    (pairT (farTranslation N p) (pairT (clock D (precision q)) payload))))

theorem fields (N p M payload : PTm n) :
    let x := config N p M payload
    let D := divisorFor N p M
    let q := analytic N p
    Γ ⊢[PRAAx] width x ≐ widthFor N p M ⋏ (divisor x ≐ D ⋏
      (latticeScale x ≐ unit q*padding D ⋏
      (translation x ≐ farTranslation N p ⋏ observationClock x ≐ clock D (precision q)))) := by
  let x := config N p M payload
  let W := widthFor N p M
  let D := divisorFor N p M
  let q := analytic N p
  let S := unit q*padding D
  let T := farTranslation N p
  let r := clock D (precision q)
  let u := pairT r payload
  let v := pairT T u
  let w := pairT S v
  let y := pairT D w
  have e₀ : Γ ⊢[PRAAx] sndT x ≐ y := snd_pair W y
  have e₁ := (congrSnd e₀).eqTrans (snd_pair D w)
  have e₂ := (congrSnd e₁).eqTrans (snd_pair S v)
  have e₃ := (congrSnd e₂).eqTrans (snd_pair T u)
  exact .andI (fst_pair W y) (.andI ((congrFst e₀).eqTrans (fst_pair D w))
    (.andI ((congrFst e₁).eqTrans (fst_pair S v)) (.andI
      ((congrFst e₂).eqTrans (fst_pair T u)) ((congrFst e₃).eqTrans (fst_pair r payload)))))

theorem bounds (N p M payload : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    let x := config N p M payload
    let q := analytic N p
    Γ ⊢[PRAAx] le one (width x) ⋏ (divisor x ≐ N*width x ⋏
      (latticeScale x ≐ GaussianDiscretePeriodicDerivativeSchedule.denominator x N p ⋏
      (le M (divisor x) ⋏ scheduled x q))) := by
  let x := config N p M payload
  let W := widthFor N p M
  let D := divisorFor N p M
  let q := analytic N p
  let T := farTranslation N p
  let R := T+num 6
  let L := budget (precision q) R one
  have f := fields (Γ := Γ) N p M payload
  have ew := f.andE₁
  have ed := f.andE₂.andE₁
  have es := f.andE₂.andE₂.andE₁
  have et := f.andE₂.andE₂.andE₂.andE₁
  have er := f.andE₂.andE₂.andE₂.andE₂
  have wz : Γ ⊢[PRAAx] le one W := zero_lt_succ _
  have wd : Γ ⊢[PRAAx] le W D := le_congr (one_mul W) (.eqRefl _) (mul_le_mul_right W hN)
  have need : Γ ⊢[PRAAx] le M (divisor x) :=
    le_congr (.eqRefl _) ed.eqSymm (le_trans (le_trans (le_add_left M L) (le_succ_self _)) wd)
  have big : Γ ⊢[PRAAx] le L D :=
    le_trans (le_trans (le_add_right L M) (le_succ_self _)) wd
  have rad : Γ ⊢[PRAAx] radius x ≐ R := congrAdd et (.eqRefl _)
  have boundEq : Γ ⊢[PRAAx] budget (precision q) (radius x) one ≐ L := by
    ipra_congr (budget (var 0) (var 1) one : PTm 2) with [.eqRefl (precision q),rad]
      using [L,GaussianBarnesCanonicalPositiveLogarithmCalculus.budget,
        GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative.budget,
        GaussianBarnesCanonicalPositiveRelativeLogarithmChart.threshold,
        GaussianBarnesCanonicalPositiveRelativeLogarithmChart.margin,
        GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.gain,one,two]
  have obsEq : Γ ⊢[PRAAx] clock (divisor x) (precision q) ≐ clock D (precision q) := by
    ipra_congr (clock (var 0) (var 1) : PTm 2) with [ed,.eqRefl (precision q)]
  have scaleEq : Γ ⊢[PRAAx] GaussianDiscretePeriodicDerivativeSchedule.denominator x N p ≐ unit q*padding D := by
    exact congrMul (.eqRefl (unit q)) (congrAdd (congrMul (.eqRefl two) ed) (.eqRefl one))
  exact .andI (le_congr (.eqRefl _) ew.eqSymm wz)
    (.andI (ed.eqTrans (congrMul (.eqRefl N) ew.eqSymm)) (.andI (es.eqTrans scaleEq.eqSymm)
      (.andI need (.andI (le_congr boundEq.eqSymm ed.eqSymm big) (.andI et (er.eqTrans obsEq.eqSymm))))))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementSchedule
