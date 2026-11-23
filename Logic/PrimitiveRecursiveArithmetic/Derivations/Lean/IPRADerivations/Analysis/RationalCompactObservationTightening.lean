import IPRADerivations.Analysis.RationalUpperRepresentation
import IPRADerivations.Analysis.RationalCubeInfimumIntervals
import IPRADerivations.Analysis.GaussianEuclideanDistanceName

/-!
# Exact compact scalar guards from two finite observation margins

A one/U observation allowance is absorbed between the original reciprocal
margin and the smaller margin 1/G when G >= 2M and U >= G. The analogous
upper guard is derived from 1-1/M. Arbitrary signed raw scalar codes are
supported; only their genuine decoded positive denominators cancel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCompactObservationTightening

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper)
open RationalSupMetric (numeratorOf denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem lower_guard (x M G U : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hG : Γ ⊢[PRAAx] le (two*M) G) (hU : Γ ⊢[PRAAx] le G U)
    (h : Γ ⊢[PRAAx] upper (fraction one M) x one U) : Γ ⊢[PRAAx]
    upper (fraction one G) x zero one := by
  let P := denominatorOf x
  let u := numeratorOf x
  let v := monus G (two*M)
  let w := monus U G
  let left := ZT.ofNat (U*P)*ZT.ofNat one
  let right := ZT.ofNat (U*M)*u+ZT.ofNat (one*M*P)
  have hmg : Γ ⊢[PRAAx] le M G := le_trans (le_add_right M M) (le_congr (by ipra_ring) (.eqRefl _) hG)
  have hg := le_trans hM hmg
  have hu := le_trans hg hU
  have hp : Γ ⊢[PRAAx] le one P := RationalArgmin.denominator_positive x
  have native : Γ ⊢[PRAAx] zle left right := RationalUpperRepresentation.upper_from_representations _ _ M P one U
    (ZT.ofNat one) u (fraction_represents _ _ hM) (RationalRepresentations.represents_self x) h
  have e := zle_toZ native
  have eg := natEq (eq_add_of_le hG)
  have eu := natEq (eq_add_of_le hU)
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat one) u G P zero one hg hp
    (fraction_represents _ _ hg) (RationalRepresentations.represents_self x)
  apply PolynomialBisection.zle_scale_cancel (c := U*M) (positive_product _ _ hu hM)
  apply zle_of_toZ (G*PolynomialBisection.slack left right+P*(G*v+w*(M+v)))
  dsimp only [left,right,P,v,w] at e ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,PolynomialBisection.slack] at e ⊢
  ipra_simps
  linear_combination 𝔞 G*e-𝔞(denominatorOf x)*(𝔞 M+𝔞(monus G (two*M)))*eu-𝔞(denominatorOf x)*𝔞 U*eg

theorem upper_guard (x M G U : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hG : Γ ⊢[PRAAx] le (two*M) G) (hU : Γ ⊢[PRAAx] le G U)
    (h : Γ ⊢[PRAAx] upper x (fraction (monus M one) M) one U) : Γ ⊢[PRAAx]
    upper x (fraction (monus G one) G) zero one := by
  let P := denominatorOf x
  let u := numeratorOf x
  let v := monus G (two*M)
  let w := monus U G
  let left := ZT.ofNat (U*M)*u
  let right := ZT.ofNat (U*P)*ZT.ofNat (monus M one)+ZT.ofNat (one*P*M)
  have hmg : Γ ⊢[PRAAx] le M G := le_trans (le_add_right M M) (le_congr (by ipra_ring) (.eqRefl _) hG)
  have hg := le_trans hM hmg
  have hu := le_trans hg hU
  have hp : Γ ⊢[PRAAx] le one P := RationalArgmin.denominator_positive x
  have native : Γ ⊢[PRAAx] zle left right := RationalUpperRepresentation.upper_from_representations _ _ P M one U
    u (ZT.ofNat (monus M one)) (RationalRepresentations.represents_self x) (fraction_represents _ _ hM) h
  have e := zle_toZ native
  have eg := natEq (eq_add_of_le hG)
  have eu := natEq (eq_add_of_le hU)
  have em := natEq (eq_add_of_le hM)
  have eG := natEq (eq_add_of_le hg)
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ u (ZT.ofNat (monus G one)) P G zero one hp hg
    (RationalRepresentations.represents_self x) (fraction_represents _ _ hg)
  apply PolynomialBisection.zle_scale_cancel (c := U*M) (positive_product _ _ hu hM)
  apply zle_of_toZ (G*PolynomialBisection.slack left right+P*(G*v+w*(M+v)))
  dsimp only [left,right,P,v,w] at e ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,PolynomialBisection.slack] at e ⊢
  ipra_simps
  linear_combination 𝔞 G*e-𝔞(denominatorOf x)*(𝔞 M+𝔞(monus G (two*M)))*eu-𝔞(denominatorOf x)*𝔞 U*eg+
    𝔞(denominatorOf x)*𝔞 U*𝔞 M*eG-𝔞(denominatorOf x)*𝔞 G*𝔞 U*em

theorem actual_scalar_compact_observation_tightening_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ (le (two*var 1) (var 2) ⋏ le (var 2) (var 3))) ⟶
      ((upper (fraction one (var 1)) (var 0) one (var 3) ⟶ upper (fraction one (var 2)) (var 0) zero one) ⋏
       (upper (var 0) (fraction (monus (var 1) one) (var 1)) one (var 3) ⟶
         upper (var 0) (fraction (monus (var 2) one) (var 2)) zero one))) := by
  apply closeUniv 4
  apply Prf.impI
  exact .andI (.impI (lower_guard _ _ _ _ Prf.hyp0.wk.andE₁ Prf.hyp0.wk.andE₂.andE₁ Prf.hyp0.wk.andE₂.andE₂ Prf.hyp0))
    (.impI (upper_guard _ _ _ _ Prf.hyp0.wk.andE₁ Prf.hyp0.wk.andE₂.andE₁ Prf.hyp0.wk.andE₂.andE₂ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalCompactObservationTightening
