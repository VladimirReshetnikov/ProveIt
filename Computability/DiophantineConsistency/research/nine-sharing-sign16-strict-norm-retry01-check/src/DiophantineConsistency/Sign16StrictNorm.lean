import DiophantineConsistency.Sign16MainNorm
import DiophantineConsistency.Sign16StrictFactor

/-! SOURCE-ONLY strict maintained norm from the retained sign16 row. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16StrictNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strict_of_seed (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (seed p) v) :
    let a := E beta v + Y beta v
    let D := (a+1)*(a+3)
    let f := v 5 + 1
    let i := v 6 + 1
    let c := C beta v
    f*f = 1 + D*(i*c*c)*(i*c*c) := by
  dsimp only
  let D := (E beta v + Y beta v + 1) * (E beta v + Y beta v + 3)
  have hpos (x : V) : 0 < x + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hD : 0 < D := by
    dsimp [D]
    apply mul_pos (hpos _)
    have h13 : (1 : V) ≤ 3 := by norm_num
    exact lt_of_lt_of_le (hpos (E beta v + Y beta v)) (by
      simpa only [add_comm] using (add_le_add_left h13 (E beta v + Y beta v)))
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
  have hscale : Scale beta v = (v 6 + 1) * D * C beta v * C beta v := by
    unfold Scale
    rw [hroot]
    ring
  have hrow := Sign16OtherRows.row06_of_seed p v hz
  change (shared33 p).evalRing (fun i => ι (v i)) * ((ι (v 5) + 1) * (ι (v 5) + 1)) -
    (shared36 p).evalRing (fun i => ι (v i)) - (shared33 p).evalRing (fun i => ι (v i)) = 0 at hrow
  have hs : (shared36 p).evalRing (fun i => ι (v i)) = ι (Scale beta v) * ι (Scale beta v) := by
    simp only [shared36, Expr.evalRing_mul, Sign16SharedValues.scale_eval p beta v hp]
  rw [Sign16MoreSharedValues.delta_eval p beta v hp, hs] at hrow
  have hrowNat : D * ((v 5 + 1) * (v 5 + 1)) = Scale beta v * Scale beta v + D := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    linarith only [hrow]
  exact Sign16StrictFactor.strict_of_factors D (v 5 + 1) (v 6 + 1) (C beta v)
    (Scale beta v) hD hscale hrowNat
end DiophantineConsistency.Sign16StrictNorm
#print axioms DiophantineConsistency.Sign16StrictNorm.strict_of_seed
