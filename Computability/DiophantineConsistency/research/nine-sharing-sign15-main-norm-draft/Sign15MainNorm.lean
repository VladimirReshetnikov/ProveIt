import DiophantineConsistency.Sign15OtherRows
import DiophantineConsistency.Sign15MoreSharedValues

/-! SOURCE-ONLY main maintained norm from the retained sign15 row. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15MainNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed15Degree124 Sign15SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_of_seed (p : Fin 4 → ℤ) (beta : V) (v : Fin 16 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (seed p) v) :
    let a := E beta v + Y beta v
    let d := Root beta v + 1
    let c := C beta v
    d*d = 1 + ((a+1)*(a+3))*c*c := by
  dsimp only
  have hr := Sign15OtherRows.row00_of_seed p v hz
  change (shared37 p).evalRing (fun i => ι (v i)) -
    (shared36 p).evalRing (fun i => ι (v i)) *
      ((shared17 p).evalRing (fun i => ι (v i)) * (shared17 p).evalRing (fun i => ι (v i))) = 0 at hr
  rw [Sign15MoreSharedValues.root_delta_eval p beta v hp,
    Sign15MoreSharedValues.delta_eval p beta v hp, Sign15SharedValues.c_eval p beta v hp] at hr
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
end DiophantineConsistency.Sign15MainNorm
#print axioms DiophantineConsistency.Sign15MainNorm.main_of_seed
