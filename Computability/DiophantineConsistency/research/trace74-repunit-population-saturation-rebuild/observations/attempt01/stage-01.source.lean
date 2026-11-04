import Trace74FixedRankPortBounds
import Trace74FixedMaskRepunitSplit
import Trace74PopulationWindow

/-! Source draft: combine same-witness repunit, rank-window and aligned Pell
    power/ordinate assumptions into the conditional 74 saturation guard.
    None of those assumptions is derived from a 74 graph zero here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74RepunitPopulationSaturation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74NaturalRankWindow Trace74RankBinding
open CompactFixedBeta CompactSymbolicPorts
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticPellRecurrence ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem guard (p : Fin 4 → ℕ) (v : Fin 10 → V) (N X Y a b j : V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀ k, 0<v k)
    (hF : v 1<q p v) (hC : v 2≤q p v)
    (hN : 0<N) (hJ : v 0=rep ((67:V)*8807) N)
    (hwindow : 3*(q p v)<rank (q p v) (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2))
    (hY : ∃ s, Y=(q p v)^3*s)
    (hX : X=Exp.exp (rank (q p v) (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2)))
    (hYpos : 0<Y) (ha : 0<a) (hb : 0<b) (hj13 : 13≤j)
    (hjR : 2*j=rank (q p v) (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2)+1)
    (hjy : 2*ycoord j (2*((X*Y)*Y-1)+1)=a+b)
    (hRy : ycoord (rank (q p v) (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2))
      (X*Y+Y)=a+Y*(a+b)) :
    let R := rank (q p v) (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2)
    (regs (Trace75Factors.ports p) (masked p v)).rank=ι R ∧
      NoCarry (v 2-1) ((lowNat:V)*v 0+1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) ∧ v 1+v 2<q p v := by
  let d : V := 67*8807
  let R := rank (q p v) (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2)
  obtain ⟨hradix,hmask⟩ := Trace74FixedMaskRepunitSplit.radix_and_mask_population N (v 0) hN hJ
  have hq : q p v=Exp.exp (d*N) := by
    change (p 0:V)*v 0+1=Exp.exp (d*N)
    rw [hp0]
    exact hradix
  have hpop : 3*(d*N)+2≤population R :=
    Trace74PopulationWindow.population_of_window (q p v) X Y a b (d*N) R j
      hq hwindow hY hX hYpos ha hb hj13 hjR hjy hRy
  exact Trace74FixedRankPortBounds.fixed_rank_saturation p v (d*N) hp0 hp2 hp3
    hv hF hC hq (le_of_eq hmask) hpop

#print axioms Trace74RepunitPopulationSaturation.guard
end Trace74RepunitPopulationSaturation
