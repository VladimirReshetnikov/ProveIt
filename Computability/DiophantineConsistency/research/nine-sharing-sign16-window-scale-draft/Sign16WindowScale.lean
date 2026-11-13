import DiophantineConsistency.Sign16MainNorm

/-! SOURCE-ONLY scale identity needed for the maintained window theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16WindowScale
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem scale_of_seed (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (seed p) v) :
    Scale beta v = (v 6 + 1) * ((E beta v + Y beta v + 1) * (E beta v + Y beta v + 3)) * C beta v * C beta v := by
  let D := (E beta v + Y beta v + 1) * (E beta v + Y beta v + 3)
  have hm := Sign16MainNorm.main_of_seed p beta v hp hz
  dsimp only at hm
  have hroot : Root beta v * (Root beta v + 2) = D * C beta v * C beta v := by
    apply ι_injective
    simp only [map_add, map_mul, map_one, map_ofNat]
    have hmi := congrArg ι hm
    simp only [map_add, map_mul, map_one, map_ofNat] at hmi
    apply sub_eq_zero.mp
    calc
      _ = (ι (Root beta v) + 1) * (ι (Root beta v) + 1) -
          (1 + ι D * ι (C beta v) * ι (C beta v)) := by ring
      _ = 0 := by
        apply sub_eq_zero.mpr
        simpa only [D, map_add, map_mul, map_one, map_ofNat] using hmi
  unfold Scale
  rw [hroot]
  ring
end DiophantineConsistency.Sign16WindowScale
#print axioms DiophantineConsistency.Sign16WindowScale.scale_of_seed
