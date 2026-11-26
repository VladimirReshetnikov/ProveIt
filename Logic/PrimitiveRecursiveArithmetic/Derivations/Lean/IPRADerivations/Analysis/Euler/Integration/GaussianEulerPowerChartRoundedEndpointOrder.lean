import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartCorrectedPanel
import IPRADerivations.AnalyticNumberTheory.CoprimeModulus
import IPRADerivations.Geometry.HypercubeSplit

/-!
# Endpoint containment from a rational observation error

An exact lower endpoint at most 1/V remains below 1/H after rounding
by 1/V if V is at least twice H. An exact upper endpoint at least V
remains above T if V is at least T+1. The inequalities below apply
to the positive denominators of the actual decoded chart samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartRoundedEndpointOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (distanceBounded)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus (pos_of_one_le)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem scalar_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat a) b := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b hb).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
  ring

theorem native_upper (a b c d V : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (hV : Γ ⊢[PRAAx] le one V)
    (hs : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) one V) :
    Γ ⊢[PRAAx] le (V*d*a) (V*b*c+b*d) := by
  have radius := scalar_coordinate_distance _ _ _ _ hV hs
  have upper := RationalValueBounds.upper_of_radius _ _ _ _ radius
  have signed := RationalUpperRepresentation.upper_from_representations _ _ b d one V (ZT.ofNat a) (ZT.ofNat c)
    (scalar_fraction a b hb) (scalar_fraction c d hd) upper
  have se := zle_toZ signed
  apply le_of_eq_add (d := PolynomialBisection.slack (ZT.ofNat (V*d)*ZT.ofNat a)
    (ZT.ofNat (V*b)*ZT.ofNat c+ZT.ofNat (one*b*d)))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at se
  simp only [PolynomialBisection.slack] at se ⊢
  ipra_simps
  linear_combination -se

theorem lower_containment (a b c d V H : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (hV : Γ ⊢[PRAAx] le one V)
    (hExact : Γ ⊢[PRAAx] le (c*V) d) (hMargin : Γ ⊢[PRAAx] le (two*H) V)
    (hs : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) one V) :
    Γ ⊢[PRAAx] le (a*H) b := by
  have rounded := native_upper a b c d V hb hd hV hs
  have cleared : Γ ⊢[PRAAx] le (d*(V*a)) (d*(two*b)) := by
    ipra_le sl rounded+𝔞 b*sl hExact
  have shrunk := le_cancel_pos (pos_of_one_le hd) cleared
  apply mul_le_cancel (d' := one)
  ipra_le (𝔞 a)*sl hMargin+sl shrunk

theorem upper_containment (a b c d V T : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (hV : Γ ⊢[PRAAx] le one V)
    (hExact : Γ ⊢[PRAAx] le (d*V) c) (hMargin : Γ ⊢[PRAAx] le (T+one) V)
    (hs : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) one V) :
    Γ ⊢[PRAAx] le (T*b) a := by
  have rounded := native_upper c d a b V hd hb hV
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hV hs)
  have cleared : Γ ⊢[PRAAx] le (d*(V*V*b)) (d*(V*a+b)) := by
    ipra_le 𝔞(V*b)*sl hExact+sl rounded
  have shrunk := le_cancel_pos (pos_of_one_le hd) cleared
  have bound : Γ ⊢[PRAAx] le (V*(T*b)+b) (V*a+b) := by
    ipra_le 𝔞(V*b)*sl hMargin+𝔞 b*sl hV+sl shrunk
  exact le_cancel_pos (pos_of_one_le hV) (le_of_add_le_add_right bound)

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartRoundedEndpointOrder
