import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeChart
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance

/-!
# Uniform Cauchy rate of the literal Barnes factorial derivatives

One retaining degree sets a common cutoff for each encoded derivative
order on the whole disk. Exact retention invariance passes the rate to
arbitrary admitted buffers, and the cutoff can be read as the total
literal product length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeCauchy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianRationalHorner (ofGaussian)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "gd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

def cutoff (p R e : PTm n) : PTm n :=
  GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff (succ p) R e e

def literalCutoff (p R e : PTm n) : PTm n := initial R+cutoff p R e

theorem rate (p z R B r s M K e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hK : Γ ⊢[PRAAx] le e (previous K))
    (hr : Γ ⊢[PRAAx] le (cutoff p R e) r) (hs : Γ ⊢[PRAAx] le (cutoff p R e) s) :
    Γ ⊢[PRAAx] independentRate F F (fd z R B r M e) (fd z R B s K e) one (unit p) := by
  let q := succ p
  let x := fd z R B r e e
  let y := fd z R B s e e
  let g := gd z R B e e
  have keep : Γ ⊢[PRAAx] le e (previous e) := le_trans (le_succ_self e) (le_succ_self (succ e))
  have left := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate q z R B r e e hz keep hr
  have right := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate q z R B s e e hz keep hs
  have both := same_denominator F G F x g y one (unit q) one (unit_positive q)
    (symmetric G F g x one (unit q) (unit_positive q) left) right
  have budget : Γ ⊢[PRAAx] ((one+one)*unit p) ≐ one*unit q :=
    (by ipra_ring : Γ ⊢[PRAAx] (one+one)*unit p ≐ unit p*two).eqTrans
      ((pw_succ two p).eqSymm.eqTrans (one_mul (unit q)).eqSymm)
  have near := GaussianNamedRateRadius.weaken F F x y (one+one) (unit q) one (unit p)
    (unit_positive q) (unit_positive p) (le_congr (.eqRefl _) budget (le_refl _)) both
  exact GaussianNamedRateTransport.transport F F F F x y (fd z R B r M e) (fd z R B s K e) one (unit p)
    (unit_positive p) near
    (GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.fixed_cross z R B r M e e hz hM keep)
    (GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.fixed_cross z R B s K e e hz hK keep)

theorem chart_rate (p z w R B D r s M K e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (hzw : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hK : Γ ⊢[PRAAx] le e (previous K))
    (hr : Γ ⊢[PRAAx] le (cutoff p R e) r) (hs : Γ ⊢[PRAAx] le (cutoff p R e) s) :
    Γ ⊢[PRAAx] independentRate F F (fd z R B r M e) (fd w R D s K e) one (unit p) :=
  GaussianNamedRateTransport.transport F F F F (fd z R B r M e) (fd z R B s K e)
    (fd z R B r M e) (fd w R D s K e) one (unit p) (unit_positive p)
    (rate p z R B r s M K e hz hM hK hr hs)
    (cross_refl _ _ (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular z R B r M e hz hM))
    (GaussianBarnesCanonicalTaylorDerivativeChart.fixed_cross w z R D B s K e hw hz hK hzw.eqSymm)

theorem literal_count (p R e N : PTm n) (hN : Γ ⊢[PRAAx] le (literalCutoff p R e) N) :
    Γ ⊢[PRAAx] le (cutoff p R e) (monus N (initial R)) ⋏
      (initial R+monus N (initial R) ≐ N) := by
  let a := initial R
  let c := cutoff p R e
  let d := monus N (literalCutoff p R e)
  have expand : Γ ⊢[PRAAx] N ≐ a+(c+d) :=
    (eq_add_of_le hN).eqTrans (add_assoc a c d)
  have sub := Common.monus_of_eq expand
  exact .andI (le_congr (.eqRefl _) sub.eqSymm (le_add_right c d))
    (eq_add_of_le (le_trans (le_add_right a c) hN)).eqSymm

theorem literal_rate (p z R B N P M K e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hK : Γ ⊢[PRAAx] le e (previous K))
    (hN : Γ ⊢[PRAAx] le (literalCutoff p R e) N) (hP : Γ ⊢[PRAAx] le (literalCutoff p R e) P) :
    Γ ⊢[PRAAx] independentRate F F (fd z R B (monus N (initial R)) M e)
      (fd z R B (monus P (initial R)) K e) one (unit p) :=
  rate p z R B (monus N (initial R)) (monus P (initial R)) M K e hz hM hK
    (literal_count p R e N hN).andE₁ (literal_count p R e P hP).andE₁

theorem actual_Barnes_literal_factorial_derivatives_uniform_Cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let N := var 4
     let P := var 5
     let M := var 6
     let K := var 7
     let e := var 8
     (source z R B ⋏ le e (previous M) ⋏ le e (previous K)) ⟶
       (le (literalCutoff p R e) N ⋏ le (literalCutoff p R e) P) ⟶
       independentRate F F (fd z R B (monus N (initial R)) M e) (fd z R B (monus P (initial R)) K e) one (unit p)) :=
  closeUniv 9 (.impI (.impI (literal_rate _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeCauchy
