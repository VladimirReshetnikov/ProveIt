import Mask79ModelBridgeV2
import Mathlib.Tactic.FinCases

/-! Natural/model realization of the gauge under explicit strict inequalities. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mask79NaturalLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive79Mask Mask79ActualRows Mask79ActualOutput Mask79ModelBridge
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def b (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := (p 0:V)*v 0
def q (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := b p v+1
def factor (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := q p v*((p 1:V)+v 5)+1

def moved (p : Fin 4 → ℕ) (v : Fin 10 → V) (z t : V) : Fin 10 → V :=
  ![v 0, v 1+b p v*t, v 2-q p v*b p v*t, v 3, v 4, v 5, v 6,
    v 7-(b p v*z+1)*factor p v*t, v 8, v 9]

theorem moved_positive (p : Fin 4 → ℕ) (v : Fin 10 → V) (z t : V)
    (hv : ∀ j, 0<v j) (hc : q p v*b p v*t<v 2)
    (hn : (b p v*z+1)*factor p v*t<v 7) : ∀ j, 0<moved p v z t j := by
  have hc' : 0<v 2-q p v*b p v*t := tsub_pos_of_lt hc
  have hn' : 0<v 7-(b p v*z+1)*factor p v*t := tsub_pos_of_lt hn
  intro j
  fin_cases j <;> simp [moved,hv,hc',hn']

theorem moved_lift (p : Fin 4 → ℕ) (v : Fin 10 → V) (z t : V)
    (hsq : let vv := fun j => ι (v j)
      (shared (integerPorts p) vv (rankTerm (integerPorts p) vv)).sq = ι z)
    (hc : q p v*b p v*t<v 2)
    (hn : (b p v*z+1)*factor p v*t<v 7) :
    let vv := fun j => ι (v j)
    let s := shared (integerPorts p) vv (rankTerm (integerPorts p) vv)
    move vv s (ι t) = fun j => ι (moved p v z t j) := by
  let vv := fun j => ι (v j)
  let s := shared (integerPorts p) vv (rankTerm (integerPorts p) vv)
  have hb : s.b = ι (b p v) := by
    change ((p 0:ℤ):DiffRing V)*ι (v 0) = ι ((p 0:V)*v 0)
    simp only [map_mul,map_natCast,Int.cast_natCast]
  have hq : s.q = ι (q p v) := by
    change ((p 0:ℤ):DiffRing V)*ι (v 0)+((1:ℤ):DiffRing V) = ι (b p v+1)
    simp only [b,map_add,map_mul,map_one,map_natCast,Int.cast_natCast,Int.cast_one]
  have hk : s.k = ι (p 1:V) := by
    change ((p 1:ℤ):DiffRing V)=ι (p 1:V)
    simp only [map_natCast,Int.cast_natCast]
  have hw : s.w = ι (v 5) := rfl
  have hsub {x y : V} (hy : y≤x) : (ι (x-y):DiffRing V)=ι x-ι y := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hy]
  have hc' := hsub (le_of_lt hc)
  have hn' := hsub (le_of_lt hn)
  change move vv s (ι t) = fun j => ι (moved p v z t j)
  funext j
  fin_cases j <;> simp [move,moved,hb,hq,hk,hw,hsq,←hc',←hn',factor,map_add,map_mul,map_one]

#print axioms Mask79NaturalLift.moved_positive
#print axioms Mask79NaturalLift.moved_lift
end Mask79NaturalLift
