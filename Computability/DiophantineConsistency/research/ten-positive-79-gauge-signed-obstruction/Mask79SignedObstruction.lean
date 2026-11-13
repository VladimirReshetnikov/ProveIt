import Mask79ModelBridgeV2
import Mask79NegativeObstruction

/-! A signed gauge move cannot map an unguarded positive F to a guarded model valuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mask79SignedObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open Mask79ActualRows Mask79ActualOutput Mask79ModelBridge Mask79NaturalLift Mask79NegativeObstruction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_guarded_lift (p : Fin 4 → ℕ) (v w : Fin 10 → V) (t : DiffRing V)
    (hFpos : 0<v 1) (hunguarded : q p v≤v 1+v 2)
    (hcast : let vv := fun j => ι (v j)
      let s := shared (integerPorts p) vv (rankTerm (integerPorts p) vv)
      move vv s t = fun j => ι (w j)) : ¬ w 1+w 2<q p w := by
  intro hguard
  let vv := fun j => ι (v j)
  let s := shared (integerPorts p) vv (rankTerm (integerPorts p) vv)
  have hb : s.b = ι (b p v) := by
    change ((p 0:ℤ):DiffRing V)*ι (v 0) = ι ((p 0:V)*v 0)
    simp only [map_mul,map_natCast,Int.cast_natCast]
  have hq : s.q = ι (q p v) := by
    change ((p 0:ℤ):DiffRing V)*ι (v 0)+((1:ℤ):DiffRing V) = ι (b p v+1)
    simp only [b,map_add,map_mul,map_one,map_natCast,Int.cast_natCast,Int.cast_one]
  change move vv s t = (fun j => ι (w j)) at hcast
  have h0 : w 0 = v 0 := by
    apply ι_injective
    have h := congrFun hcast 0
    change vv 0 = ι (w 0) at h
    exact h.symm
  have hF : (ι (w 1):DiffRing V)=ι (v 1)+ι (b p v)*t := by
    have h := congrFun hcast 1
    change vv 1+s.b*t = ι (w 1) at h
    simpa only [vv,hb] using h.symm
  have hC : (ι (w 2):DiffRing V)=ι (v 2)-ι (q p v)*ι (b p v)*t := by
    have h := congrFun hcast 2
    change vv 2-s.q*s.b*t = ι (w 2) at h
    simpa only [vv,hq,hb] using h.symm
  have hwq : q p w=q p v := by simp only [q,b,h0]
  rw [hwq] at hguard
  rcases nonneg_or_nonpos t with ⟨u,ht⟩ | ⟨u,ht⟩
  · by_cases hu : u=0
    · subst u
      simp only [map_zero] at ht
      rw [ht] at hF hC
      simp only [mul_zero,add_zero,sub_zero] at hF hC
      have hw1 := ι_injective hF
      have hw2 := ι_injective hC
      rw [hw1,hw2] at hguard
      exact (not_lt_of_ge hunguarded) hguard
    · have hu1 : 1≤u := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hu)
      have hF1 : 1≤v 1 := pos_iff_one_le.mp hFpos
      have hbmul : b p v≤b p v*u := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 (zero_le : 0≤b p v)
      have hw1 : w 1=v 1+b p v*u := by
        apply ι_injective
        rw [ht] at hF
        simpa only [map_add,map_mul] using hF
      have hqle : q p v≤w 1 := by
        rw [hw1]
        unfold q
        calc
          b p v+1≤b p v*u+v 1 := add_le_add hbmul hF1
          _ = v 1+b p v*u := add_comm _ _
      have hw1le : w 1≤w 1+w 2 := le_add_of_nonneg_right (zero_le : 0≤w 2)
      exact (not_lt_of_ge (le_trans hqle hw1le)) hguard
  · rw [ht] at hF hC
    have hFneg : (ι (w 1):DiffRing V)=ι (v 1)-ι (b p v*u) := by
      simpa only [mul_neg,sub_eq_add_neg,map_mul] using hF
    have hCneg : (ι (w 2):DiffRing V)=ι (v 2)+ι (q p v*b p v*u) := by
      simpa only [mul_neg,sub_neg_eq_add,map_mul] using hC
    have hbound : b p v*u≤v 1 := by
      apply ι_le_ι.mp
      apply sub_nonneg.mp
      rw [← hFneg]
      exact ι_nonneg _
    have hsub {x y : V} (hy : y≤x) : (ι (x-y):DiffRing V)=ι x-ι y := by
      apply eq_sub_iff_add_eq.mpr
      rw [←map_add,tsub_add_cancel_of_le hy]
    have hw1 : w 1=v 1-b p v*u := by
      apply ι_injective
      exact hFneg.trans (hsub hbound).symm
    have hw2 : w 2=v 2+q p v*b p v*u := by
      apply ι_injective
      simpa only [map_add,map_mul] using hCneg
    rw [hw1,hw2] at hguard
    exact no_negative_guard p v u hbound hunguarded hguard

#print axioms Mask79SignedObstruction.no_guarded_lift
end Mask79SignedObstruction
