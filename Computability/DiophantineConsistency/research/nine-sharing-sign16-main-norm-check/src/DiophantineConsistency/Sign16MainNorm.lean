import DiophantineConsistency.Sign16OtherRows
import DiophantineConsistency.Sign16MoreSharedValues

/-! SOURCE-ONLY main maintained norm from the retained sign16 row. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16MainNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_of_seed (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (seed p) v) :
    let a := E beta v + Y beta v
    let d := Root beta v + 1
    let c := C beta v
    d*d = 1 + ((a+1)*(a+3))*c*c := by
  dsimp only
  have hr := Sign16OtherRows.row00_of_seed p v hz
  change (shared34 p).evalRing (fun i => ι (v i)) -
    (shared33 p).evalRing (fun i => ι (v i)) *
      ((shared18 p).evalRing (fun i => ι (v i)) * (shared18 p).evalRing (fun i => ι (v i))) = 0 at hr
  rw [Sign16MoreSharedValues.root_delta_eval p beta v hp,
    Sign16MoreSharedValues.delta_eval p beta v hp, Sign16SharedValues.c_eval p beta v hp] at hr
  apply ι_injective
  simp only [map_add, map_mul, map_one, map_ofNat]
  apply sub_eq_zero.mp
  calc
    _ = ι (Root beta v * (Root beta v + 2)) -
      ι ((E beta v + Y beta v + 1) * (E beta v + Y beta v + 3)) *
        (ι (C beta v) * ι (C beta v)) := by
          simp only [map_add, map_mul, map_ofNat, map_one]
          ring
    _ = 0 := hr
end DiophantineConsistency.Sign16MainNorm
#print axioms DiophantineConsistency.Sign16MainNorm.main_of_seed
