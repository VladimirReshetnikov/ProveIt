import Trace74FixedRankSaturation
import DiophantineConsistency.CompactFixedBeta

/-! Source draft: supply the three symbolic-port inequalities from the
    selected fixed-beta bounds. All individual, radix and population premises
    remain explicit and are not derived from a graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedRankPortBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74NaturalRankWindow Trace74RankBinding
open Trace74FixedRankSaturation CompactFixedBeta CompactSymbolicPorts
open ArithmeticBinaryPopulation ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_rank_saturation (K : ℕ) (v : Fin 10 → V) (u : V)
    (hv : ∀ j, 0<v j)
    (hF : v 1<q (fixedPorts K) v) (hC : v 2≤q (fixedPorts K) v)
    (hexp : q (fixedPorts K) v=Exp.exp u)
    (hpopulation : population ((lowNat:V)*v 0+1)+population ((highNat:V)*v 0-1)≤u+2)
    (hrank : 3*u+2≤population
      (rank (q (fixedPorts K) v) (lowNat:V) ((betaNat+highNat:ℕ):V)
        (v 0) (v 1) (v 2))) :
    let R := rank (q (fixedPorts K) v) (lowNat:V) ((betaNat+highNat:ℕ):V)
      (v 0) (v 1) (v 2)
    (regs (Trace75Factors.ports (fixedPorts K)) (masked (fixedPorts K) v)).rank=ι R ∧
      NoCarry (v 2-1) ((lowNat:V)*v 0+1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) ∧ v 1+v 2<q (fixedPorts K) v := by
  have hb := CompactFixedBeta.bounds (v 0) (hv 0)
  have hlow : (lowNat:V)<(betaNat:V) := by
    change CompactConcreteIncrement.mask<(betaNat:V)
    exact hb.2.1
  have hhigh : (highNat:V)≤(betaNat:V) := by
    have h : (betaNat:V)+(highNat:V)<(betaNat:V)+(betaNat:V) := by
      change (betaNat:V)+((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)<_
      simpa only [two_mul] using hb.2.2.1
    exact le_of_lt ((add_lt_add_iff_left (betaNat:V)).mp h)
  have hhighJ : 1≤(highNat:V)*v 0 := by
    change 1≤((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V)*v 0
    exact hb.2.2.2
  exact Trace74FixedRankSaturation.fixed_rank_saturation K v u hv hF hC hexp
    hlow hhigh hhighJ hpopulation hrank

#print axioms Trace74FixedRankPortBounds.fixed_rank_saturation
end Trace74FixedRankPortBounds
