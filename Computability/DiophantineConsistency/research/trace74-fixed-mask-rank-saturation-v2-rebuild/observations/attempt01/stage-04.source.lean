import Trace74RankBinding
import Trace74NaturalBlock
import Trace74FixedMaskSaturationGuard

/-! Source draft: bind the actual 74 signed rank to the fixed-mask conditional
    saturation theorem. Individual ranges, radix and population assumptions
    are explicit; this does not derive them from a 74 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedRankSaturation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74NaturalRankWindow
open Trace74RankBinding CompactFixedBeta CompactSymbolicPorts
open ArithmeticBinaryPopulation ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fixedPorts (K : ℕ) : Fin 4 → ℕ := CompactSymbolicPorts.ports betaNat K lowNat highNat

theorem fixed_rank_saturation (K : ℕ) (v : Fin 10 → V) (u : V)
    (hv : ∀ j, 0<v j)
    (hF : v 1<q (fixedPorts K) v) (hC : v 2≤q (fixedPorts K) v)
    (hexp : q (fixedPorts K) v=Exp.exp u)
    (hLow : (lowNat:V)<(betaNat:V))
    (hHigh : (highNat:V)≤(betaNat:V)) (hHighJ : 1≤(highNat:V)*v 0)
    (hpopulation : population ((lowNat:V)*v 0+1)+population ((highNat:V)*v 0-1)≤u+2)
    (hrank : 3*u+2≤population
      (rank (q (fixedPorts K) v) (lowNat:V) ((betaNat+highNat:ℕ):V)
        (v 0) (v 1) (v 2))) :
    let R := rank (q (fixedPorts K) v) (lowNat:V) ((betaNat+highNat:ℕ):V)
      (v 0) (v 1) (v 2)
    (regs (Trace75Factors.ports (fixedPorts K)) (masked (fixedPorts K) v)).rank=ι R ∧
      NoCarry (v 2-1) ((lowNat:V)*v 0+1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) ∧ v 1+v 2<q (fixedPorts K) v := by
  let Q := q (fixedPorts K) v
  let R := rank Q (lowNat:V) ((betaNat+highNat:ℕ):V) (v 0) (v 1) (v 2)
  have hQ : Q=(betaNat:V)*v 0+1 := by
    simp only [Q,q,b,fixedPorts,CompactSymbolicPorts.ports,Fin.isValue,Matrix.cons_val_zero]
  have hR : (regs (Trace75Factors.ports (fixedPorts K)) (masked (fixedPorts K) v)).rank=ι R := by
    exact graph_rank_eval (fixedPorts K) v hF hC
  have hRshape : (ι R : DiffRing V) =
      ((ι Q)*((ι Q)-(ι (v 1)))-(ι (v 2)))*((ι Q)^2-1)+
        ((ι (lowNat:V))+(ι Q)*((ι (betaNat:V))+(ι (highNat:V))))*(ι (v 0)) := by
    dsimp [R,rank]
    simp only [map_add,map_mul,map_natCast,Nat.cast_add]
    have h := hF
    have hqf : v 1≤Q := le_of_lt h
    have hqfpos : 0<Q-v 1 := tsub_pos_iff_lt.mpr h
    have hcmul : v 2≤Q*(Q-v 1) := le_trans hC
      (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hqfpos))
    have hqpos : 0<Q := lt_of_lt_of_le (hv 2) hC
    have hq2 : 1≤Q^2 := by
      simpa only [pow_two] using one_le_mul (pos_iff_one_le.mp hqpos) (pos_iff_one_le.mp hqpos)
    have cast_sub (a b : V) (hab : b≤a) : (ι (a-b):DiffRing V)=ι a-ι b := by
      apply eq_sub_iff_add_eq.mpr
      rw [←map_add,tsub_add_cancel_of_le hab]
    rw [cast_sub (Q*(Q-v 1)) (v 2) hcmul, map_mul, cast_sub Q (v 1) hqf,
      cast_sub (Q^2) 1 hq2]
    simp only [map_mul,map_pow,map_one]
  have hblock := Trace74NaturalBlock.natural_block Q (betaNat:V) (v 0) (v 1) (v 2)
    (lowNat:V) (highNat:V) R hQ (hv 2) hC hF hHighJ hRshape
  have hA : v 2-1<Q := lt_of_lt_of_le (tsub_lt_self (hv 2) (by simp)) hC
  have hM : (lowNat:V)*v 0+1<Q := by
    rw [hQ]
    simpa only [add_comm] using add_lt_add_right (mul_lt_mul_of_pos_right hLow (hv 0)) 1
  have hs := Trace74FixedMaskSaturationGuard.guard u Q (v 0) (v 1) (v 2) R
    hexp hQ (hv 0) hHighJ hHigh (hv 2) hA hF hM hblock hpopulation hrank
  exact ⟨hR,hs⟩

#print axioms Trace74FixedRankSaturation.fixed_rank_saturation
end Trace74FixedRankSaturation
